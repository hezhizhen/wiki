"""Format and clean a Logseq OG export, then set its public home page.

    uv run scripts/prepare.py
    uv run scripts/prepare.py --check
    uv run scripts/prepare.py --write

Default: preview only. The home page must be present and marked public.
Write mode replaces index.html once after all stages pass.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import sys
import tempfile
import unicodedata
from html import escape
from pathlib import Path
from typing import Any

from format import (
    Collection,
    PayloadError,
    Script,
    ScriptParser,
    WriteDurabilityError,
    compact_state,
    edn_signature,
    extract,
    extract_document,
    format_html,
    parse_state,
    read_export,
    replace_regions,
    serialize_payload,
    state_mapping,
    unpack_database,
    write_export,
)
from sanitize import (
    TransitCacheExpander,
    clean_html,
    database_parts,
    normalize_hidden_properties,
    plain_string,
    repo_configuration,
    transit_map,
)

HOME_PAGE = "Wiki Index"
PAGE_REFERENCE_FILTER_ID = "wiki-page-reference-filter"
PAGE_REFERENCE_FILTER = """(() => {
  const root = document.getElementById("root");
  if (!root) return;

  const pages = new Set(JSON.parse(document.currentScript.getAttribute("data-pages")));
  const selector = "a.page-ref[data-ref]:not([href]), a.tag[data-ref]:not([href])";
  const marker = "data-wiki-unavailable-page";
  const unavailable = (link) => !pages.has(link.getAttribute("data-ref"));
  const style = document.createElement("style");
  style.textContent = `
    a[${marker}] {
      color: inherit !important;
      text-decoration: none !important;
      pointer-events: none;
    }
    a[${marker}] :is(a.page-ref, a.tag):not([${marker}]) {
      pointer-events: auto;
    }
  `;
  document.head.append(style);

  const update = () => {
    for (const link of root.querySelectorAll(selector)) {
      if (unavailable(link)) {
        link.setAttribute(marker, "");
        link.removeAttribute("tabindex");
      } else if (link.hasAttribute(marker)) {
        link.removeAttribute(marker);
        link.tabIndex = 0;
      }
    }
  };
  // Logseq renders page references asynchronously and can reuse them on navigation.
  new MutationObserver(update).observe(root, {
    childList: true, subtree: true, attributes: true, attributeFilter: ["data-ref"]
  });
  update();

  // Logseq handles these actions itself, including on anchors without an href.
  for (const type of ["click", "mouseup", "keyup", "dragstart"]) {
    root.addEventListener(type, (event) => {
      const link = event.target instanceof Element && event.target.closest(selector);
      if (link && unavailable(link)) {
        event.preventDefault();
        event.stopPropagation();
      }
    }, true);
  }
})();"""


def require_home_page(database: str) -> list[str]:
    """Return the exported page names after verifying the public home page."""
    wire = TransitCacheExpander().expand(unpack_database(database))
    _, datoms = database_parts(wire)
    records = [datom[1] for datom in datoms]
    # Match Logseq OG's page-name-sanity-lc.
    name = unicodedata.normalize(
        "NFC", HOME_PAGE.lower().removeprefix("/").removesuffix("/")
    )
    pages = [
        (row[0], plain_string(row[2])) for row in records if row[1] == "~:block/name"
    ]
    home = [eid for eid, page_name in pages if page_name == name]
    if len(home) != 1:
        raise PayloadError(
            f"导出中未找到唯一的 {HOME_PAGE} 页面，请先在 Logseq 中导出该页。"
        )
    properties = [
        row[2]
        for row in records
        if row[0] == home[0] and row[1] == "~:block/properties"
    ]
    if len(properties) != 1 or transit_map(properties[0]).get("~:public") is not True:
        raise PayloadError(f"导出的 {HOME_PAGE} 页面未标记为 public:: true。")
    return sorted({page_name for _, page_name in pages if page_name is not None})


def value_index(mapping: Collection, key: str) -> int | None:
    """Return the value position for a keyword in a parsed EDN map."""
    # parse_state checks the map for duplicate keys before lookup.
    for index in range(0, len(mapping.children), 2):
        if mapping.children[index] == key:
            return index + 1
    return None


def child_collection(mapping: Collection, key: str, *, opener: str = "{") -> Collection:
    index = value_index(mapping, key)
    if index is None:
        value = Collection(opener, [])
        mapping.children.extend([key, value])
        return value
    value = mapping.children[index]
    if value == "nil":
        value = Collection(opener, [])
        mapping.children[index] = value
    if not isinstance(value, Collection) or value.opener != opener:
        raise PayloadError(f"导出配置项 {key} 的数据结构不符合预期，已停止。")
    return value


def page_reference_filter_region(
    document: ScriptParser, loader: Script, page_names: list[str]
) -> tuple[int, int, str]:
    scripts = [
        script
        for script in document.scripts
        if script.attrs.get("id") == PAGE_REFERENCE_FILTER_ID
    ]
    if document.ids[PAGE_REFERENCE_FILTER_ID] != len(scripts) or len(scripts) > 1:
        raise PayloadError("页面中的页引用过滤脚本 id 发生冲突。")
    existing = scripts[0] if scripts else None
    indent = existing.indent if existing else loader.indent
    pages = escape(json.dumps(page_names, separators=(",", ":")), quote=True)
    body = "\n".join(
        indent + "  " + line if line else ""
        for line in PAGE_REFERENCE_FILTER.splitlines()
    )
    markup = (
        f'<script id="{PAGE_REFERENCE_FILTER_ID}" data-pages="{pages}">\n'
        f"{body}\n{indent}</script>"
    )
    if existing:
        return existing.start, existing.end, markup
    return loader.end, loader.end, "\n" + indent + markup


def set_home_html(html: str) -> tuple[str, dict[str, Any]]:
    document = ScriptParser(html)
    _, database = extract_document(document, "logseq_db")
    page_names = require_home_page(database)
    payload, original_state = extract_document(document, "logseq_state")
    state = parse_state(original_state)
    original_signature = edn_signature(original_state)

    _, config = repo_configuration(state_mapping(state))
    hidden_key = ":block-hidden-properties"
    index = value_index(config, hidden_key)
    if index is not None:
        config.children[index] = normalize_hidden_properties(config.children[index])
    hidden_properties = child_collection(config, hidden_key, opener="#{")
    if ":public" not in hidden_properties.children:
        hidden_properties.children.append(":public")

    home = child_collection(config, ":default-home")
    index = value_index(home, ":page")
    page = json.dumps(HOME_PAGE)
    if index is None:
        home.children.extend([":page", page])
    else:
        home.children[index] = page

    report = {
        "home_page": HOME_PAGE,
        "hidden_property": "public",
    }
    # Derive the expected tokens independently of the pretty renderer.
    updated_state = compact_state(state)
    expected_signature = edn_signature(updated_state)
    replacements = [page_reference_filter_region(document, payload.loader, page_names)]
    if expected_signature != original_signature:
        replacements.append(
            (payload.start(), payload.end(), serialize_payload(payload, updated_state))
        )
    updated = replace_regions(html, replacements)
    database_preserved = extract(updated, "logseq_db")[1] == database
    if (
        not database_preserved
        or edn_signature(extract(updated, "logseq_state")[1]) != expected_signature
    ):
        raise PayloadError("更新导出配置后的嵌入数据校验失败，已停止。")
    return updated, {
        **report,
        "database_preserved": database_preserved,
        "changed": updated != html,
    }


def save_snapshots(wiki_dir: Path, original: bytes, prepared: bytes) -> Path:
    """Save both versions in a private directory outside the export."""
    root = Path("/tmp").resolve(strict=True)
    if any(parent.samefile(wiki_dir) for parent in (root, *root.parents)):
        raise PayloadError("对照目录必须位于 wiki 导出目录之外。")
    directory = Path(tempfile.mkdtemp(prefix="wiki-prepare-", dir=root))
    try:
        for name, content in (("original.html", original), ("prepared.html", prepared)):
            with (directory / name).open("xb") as handle:
                os.fchmod(handle.fileno(), 0o600)
                handle.write(content)
    except BaseException:
        shutil.rmtree(directory, ignore_errors=True)
        raise
    return directory


def main() -> int:
    parser = argparse.ArgumentParser(
        description=f"格式化并清洗 wiki 导出，设置首页 {HOME_PAGE} 并隐藏 public 属性。默认只预览。"
    )
    parser.add_argument(
        "--wiki-dir",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="wiki 导出目录；默认是脚本所在 scripts 目录的上一级",
    )
    parser.add_argument(
        "--debug",
        action="store_true",
        help="调试时将原始导出和处理结果保存到 /tmp 下的私有目录",
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--write", action="store_true", help="所有阶段通过后，仅原子替换 index.html"
    )
    mode.add_argument(
        "--check", action="store_true", help="只检查，发布结果需要更新时退出码为 1"
    )
    args = parser.parse_args()
    stage = "读取导出"
    snapshot_dir = None
    try:
        target, original, info = read_export(args.wiki_dir.resolve(strict=True))
        html = original.decode("utf-8")
        stage = "格式化"
        html, format_report = format_html(html)
        stage = "清洗"
        html, sanitize_report = clean_html(html)
        stage = "首页设置"
        html, home_report = set_home_html(html)
        prepared = html.encode("utf-8")
        changed = prepared != original
        written = args.write and changed
        if args.debug:
            stage = "保存对照文件"
            snapshot_dir = save_snapshots(target.parent, original, prepared)
        if args.write:
            stage = "写入发布文件"
            write_export(target, original, prepared, info)
        report = {
            "changed": changed,
            "mode": "write" if args.write else "check" if args.check else "preview",
            "written": written,
            "format": format_report,
            "sanitize": sanitize_report,
            "configure": home_report,
        }
        if snapshot_dir is not None:
            report["snapshot_dir"] = str(snapshot_dir)
        print(json.dumps(report, ensure_ascii=False, indent=2))
        return 1 if args.check and changed else 0
    except WriteDurabilityError as error:
        print(str(error), file=sys.stderr)
        status = 3
    except (PayloadError, OSError, RecursionError, ValueError) as error:
        message = (
            str(error)
            if isinstance(error, (PayloadError, OSError))
            else type(error).__name__
        )
        print(f"未完成{stage}：{message}", file=sys.stderr)
        status = 2
    if snapshot_dir is not None:
        print(f"对照文件已保存在 {snapshot_dir}", file=sys.stderr)
    return status


if __name__ == "__main__":
    raise SystemExit(main())
