"""Expand the database and configuration inside a Logseq OG HTML export.

Only the two embedded data regions are formatted. All other HTML, including
existing loader tags, attributes and whitespace, is preserved byte for byte.
The publication pipeline applies its cleaning rules after formatting.
"""

from __future__ import annotations

import errno
import hashlib
import json
import math
import os
import re
import stat
import tempfile
from collections import Counter
from contextlib import contextmanager
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path
from typing import Any


class PayloadError(Exception):
    """Unsupported or ambiguous export data; messages exclude payload values."""


class CleanError(PayloadError):
    """A rejected input or failed integrity check; messages omit private data."""


class WriteDurabilityError(CleanError):
    """Replacement succeeded, but parent-directory durability is unconfirmed."""


DATA_IDS = {"logseq_db": "logseq-db-data", "logseq_state": "logseq-state-data"}
DATA_TYPES = {"logseq_db": "application/json", "logseq_state": "application/edn"}
# HTML replaces raw NUL and UTF-8 cannot encode lone surrogates.
UNSAFE_SCRIPT_CONTENT = re.compile(r"[\x00\ud800-\udfff]|<!--|</?script", re.IGNORECASE)
ESCAPE_PREFIX = "logseq____&"
# Replacement order in the Logseq OG exporter.
LOGSEQ_ENTITIES = (("amp", "&"), ("lt", "<"), ("gt", ">"), ("quot", '"'), ("apos", "'"))


class TransitText(str):
    """Transit JSON text, rather than a legacy Logseq-escaped string."""


def load_json(text: str, *, strict: bool = True) -> Any:
    def reject(_value: str) -> Any:
        raise PayloadError("嵌入 JSON 包含非有限数值。")

    def finite_float(token: str) -> float:
        value = float(token)
        return value if math.isfinite(value) else reject(token)

    def mapping(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result = {}
        for key, value in pairs:
            if key in result:
                raise PayloadError("JSON 包含重复的键，拒绝格式化。")
            result[key] = value
        return result

    try:
        # Preserve the sign of a JSON -0 token.
        return json.loads(
            text,
            strict=strict,
            parse_constant=reject,
            parse_float=finite_float,
            parse_int=lambda value: -0.0 if value == "-0" else int(value),
            object_pairs_hook=mapping,
        )
    except (ValueError, OverflowError) as error:
        raise PayloadError("嵌入 JSON 格式异常。") from error


def unpack_database(payload: str) -> Any:
    if not isinstance(payload, TransitText):
        # Undo the exporter's replacements in reverse. Decoding ampersands
        # last keeps a literal Logseq marker from being decoded a second time.
        for name, char in reversed(LOGSEQ_ENTITIES):
            payload = payload.replace(ESCAPE_PREFIX + name + ";", char)
    return load_json(payload)


def dump_database(value: Any, **kwargs: Any) -> str:
    try:
        return json.dumps(value, allow_nan=False, **kwargs)
    except (TypeError, ValueError) as error:
        raise PayloadError("无法将隐藏数据库编码为有效 JSON。") from error


def pack_database(value: Any) -> str:
    payload = dump_database(value, ensure_ascii=True, separators=(",", ":"))
    for name, char in LOGSEQ_ENTITIES:
        payload = payload.replace(char, ESCAPE_PREFIX + name + ";")
    return payload


def html_safe_json(text: str) -> str:
    # A script data block still has raw-text end tags. Logseq also unescapes
    # entity markers before reading the JSON, so no literal ampersands survive.
    return (
        text.translate(
            {
                ord("&"): r"\u0026",
                ord("<"): r"\u003c",
                ord(">"): r"\u003e",
                0x2028: r"\u2028",
                0x2029: r"\u2029",
            }
        )
        .encode("utf-8", "backslashreplace")
        .decode("utf-8")
    )


def transit_text(value: Any) -> TransitText:
    return TransitText(
        html_safe_json(dump_database(value, ensure_ascii=True, separators=(",", ":")))
    )


def pretty_database(value: Any) -> str:
    def compact(node: Any) -> str:
        return dump_database(node, ensure_ascii=False, separators=(", ", ": "))

    def render(node: Any, level: int = 0) -> str:
        pad = "  " * level
        if not isinstance(node, (list, dict)) or not node:
            return pad + compact(node)
        if isinstance(node, list):
            small = node[0] == "~#datascript/Datom" or all(
                not isinstance(child, (list, dict)) for child in node
            )
            if small:
                line = compact(node)
                if len(pad) + len(line) <= 120:
                    return pad + line
            return (
                pad
                + "[\n"
                + ",\n".join(render(child, level + 1) for child in node)
                + "\n"
                + pad
                + "]"
            )
        lines = []
        for key, child in node.items():
            part = render(child, level + 1)
            lines.append("  " * (level + 1) + compact(key) + ": " + part.lstrip())
        return pad + "{\n" + ",\n".join(lines) + "\n" + pad + "}"

    return html_safe_json(render(value))


# Logseq's ClojureScript reader uses ECMAScript \s plus commas.
EDN_WHITESPACE = frozenset(
    " \t\n\r\v\f,\u00a0\u1680\u2000\u2001\u2002\u2003\u2004\u2005"
    "\u2006\u2007\u2008\u2009\u200a\u2028\u2029\u202f\u205f\u3000\ufeff"
)
EDN_CONTROL_ESCAPES = {codepoint: rf"\u{codepoint:04x}" for codepoint in range(0x20)}


def edn_tokens(text: str, *, allow_comments: bool = False) -> list[str]:
    """Tokenize the printed EDN subset used by exported app configuration.

    Collections, strings, characters, symbols, keywords, and tagged values are
    preserved. Reader comments are accepted only for source queries.
    """
    tokens: list[str] = []
    index = 0
    while index < len(text):
        char = text[index]
        if char in EDN_WHITESPACE:
            index += 1
            continue
        if char == ";" and allow_comments:
            while index < len(text) and text[index] not in "\r\n":
                index += 1
            continue
        if char == ";" or char in "'^`~":
            raise PayloadError("配置包含尚未支持的 EDN 读取语法，已停止。")
        if text.startswith("#{", index):
            tokens.append("#{")
            index += 2
            continue
        if char in "{}[]()":
            tokens.append(char)
            index += 1
            continue
        start = index
        if char == '"':
            index += 1
            while index < len(text):
                if text[index] == "\\":
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            else:
                raise PayloadError("配置包含未结束的字符串。")
            literal = text[start:index]
            # pr-str can emit raw controls. Keep tokens safe for JSON consumers.
            load_json(literal, strict=False)
            tokens.append(literal.translate(EDN_CONTROL_ESCAPES))
            continue
        elif char == "\\":
            index += 1
            if index == len(text):
                raise PayloadError("配置中的字符字面量不完整。")
            if text[index] in '{}[]();"\\' or text[index] in EDN_WHITESPACE:
                index += 1
            else:
                while (
                    index < len(text)
                    and text[index] not in EDN_WHITESPACE
                    and text[index] not in "{}[]();"
                ):
                    index += 1
        else:
            while (
                index < len(text)
                and text[index] not in EDN_WHITESPACE
                and text[index] not in '{}[]();"'
            ):
                index += 1
            token = text[start:index]
            if (
                not token
                or token.startswith(("#_", "#=", "#:", "#?", "#!"))
                or token == "#"
            ):
                raise PayloadError("配置包含尚未支持的 EDN 读取语法，已停止。")
        tokens.append(text[start:index])
    return tokens


def edn_signature(text: str) -> list[Any]:
    return [
        ("string", load_json(token)) if token.startswith('"') else ("token", token)
        for token in edn_tokens(text)
    ]


@dataclass
class Collection:
    opener: str
    children: list[Any]


@dataclass
class Tagged:
    tag: str
    value: Any


def parse_state(text: str, *, allow_comments: bool = False) -> Collection:
    """Parse one configuration map without executing any of its forms."""
    tokens = edn_tokens(text, allow_comments=allow_comments)
    index = 0
    closers = {"{": "}", "#{": "}", "[": "]", "(": ")"}

    def parse() -> Any:
        nonlocal index
        if index >= len(tokens):
            raise PayloadError("配置中的表达式不完整。")
        token = tokens[index]
        index += 1
        if token in closers:
            children = []
            while index < len(tokens) and tokens[index] != closers[token]:
                children.append(parse())
            if index == len(tokens) or (token == "{" and len(children) % 2):
                raise PayloadError("配置集合未闭合或映射键值不成对。")
            index += 1
            return Collection(token, children)
        if token in "}])":
            raise PayloadError("配置集合的括号不匹配。")
        if token.startswith("#") and token not in ("##Inf", "##-Inf", "##NaN"):
            if UNSAFE_SCRIPT_CONTENT.search(token):
                raise PayloadError("配置标签包含无法安全内嵌的 HTML 序列。")
            return Tagged(token, parse())
        return token

    root = parse()
    if index != len(tokens) or not isinstance(root, Collection) or root.opener != "{":
        raise PayloadError("发布配置必须是单个 EDN 映射。")
    edn_value(root)  # Reject duplicate map keys, including escaped string keys.
    return root


def edn_value(node: Any) -> Any:
    """Return a hashable, typed representation for semantic comparisons."""
    if isinstance(node, str):
        return ("string", load_json(node)) if node.startswith('"') else ("atom", node)
    if isinstance(node, Tagged):
        return ("tag", node.tag, edn_value(node.value))
    children = [edn_value(child) for child in node.children]
    if node.opener == "{":
        pairs = list(zip(children[::2], children[1::2]))
        if len({key for key, _ in pairs}) != len(pairs):
            raise PayloadError("配置映射包含重复的键。")
        return ("map", tuple(sorted(pairs, key=repr)))
    if node.opener == "#{":
        return ("set", tuple(sorted(children, key=repr)))
    return (node.opener, tuple(children))


def state_mapping(node: Any) -> dict[str, Any]:
    """Access a map with simple EDN keys, preserving key types and spelling."""
    if not isinstance(node, Collection) or node.opener != "{":
        raise PayloadError("预期配置项是 EDN 映射。")
    edn_value(node)
    if any(not isinstance(key, str) for key in node.children[::2]):
        raise PayloadError("配置项使用了不支持的复杂键。")
    return dict(zip(node.children[::2], node.children[1::2]))


def state_semantics(text: str) -> Any:
    return edn_value(parse_state(text))


def compact_state(node: Any) -> str:
    if isinstance(node, str):
        return node
    if isinstance(node, Tagged):
        return node.tag + " " + compact_state(node.value)
    close = {"{": "}", "#{": "}", "[": "]", "(": ")"}[node.opener]
    if node.opener == "{":
        parts = [
            compact_state(key) + " " + compact_state(value)
            for key, value in zip(node.children[::2], node.children[1::2])
        ]
        return "{" + ", ".join(parts) + "}"
    return (
        node.opener + " ".join(compact_state(child) for child in node.children) + close
    )


def render_state(root: Collection) -> str:
    """Print a configuration syntax tree using the export's readable format."""
    closers = {"{": "}", "#{": "}", "[": "]", "(": ")"}

    def leaf(token: str) -> str:
        if token.startswith('"'):
            token = json.dumps(load_json(token), ensure_ascii=False)
            return (
                token.replace("<", r"\u003c")
                .replace("\u2028", r"\u2028")
                .replace("\u2029", r"\u2029")
                .encode("utf-8", "backslashreplace")
                .decode("utf-8")
            )
        if UNSAFE_SCRIPT_CONTENT.search(token):
            raise PayloadError("配置符号包含无法安全内嵌的 HTML 序列。")
        return token

    def inline(node: Any) -> str | None:
        if isinstance(node, str):
            return leaf(node)
        if isinstance(node, Tagged):
            value = inline(node.value)
            return node.tag + " " + value if value is not None else None
        if node.opener == "{" and node.children:
            return None
        parts = [inline(child) for child in node.children]
        if any(part is None for part in parts):
            return None
        result = node.opener + " ".join(parts) + closers[node.opener]
        return result if len(result) <= 90 else None

    def render(node: Any, level: int = 0) -> list[str]:
        pad = "  " * level
        short = inline(node)
        if short is not None:
            return [pad + short]
        if isinstance(node, Tagged):
            result = render(node.value, level)
            result[0] = pad + node.tag + " " + result[0].lstrip()
            return result
        result = [pad + node.opener]
        if node.opener == "{":
            for position in range(0, len(node.children), 2):
                key, value = node.children[position : position + 2]
                key_text = inline(key)
                value_lines = render(value, level + 1)
                if key_text is not None:
                    value_text = value_lines[0].lstrip(" ")
                    result.append("  " * (level + 1) + key_text + " " + value_text)
                    result.extend(value_lines[1:])
                else:
                    result.extend(render(key, level + 1))
                    result.extend(value_lines)
        else:
            for child in node.children:
                result.extend(render(child, level + 1))
        return result + [pad + closers[node.opener]]

    return "\n".join(render(root))


def pretty_state(text: str) -> str:
    output = render_state(parse_state(text))
    if edn_signature(output) != edn_signature(text):
        raise PayloadError("格式化改变了配置内容，已停止。")
    return output


@dataclass
class Script:
    source: str
    start: int
    body_start: int
    body_end: int
    end: int
    attrs: dict[str, str | None]

    @property
    def body(self) -> str:
        return self.source[self.body_start : self.body_end]

    @property
    def opening(self) -> str:
        return self.source[self.start : self.body_start]

    @property
    def closing(self) -> str:
        return self.source[self.body_end : self.end]

    @property
    def indent(self) -> str:
        prefix = self.source[self.source.rfind("\n", 0, self.start) + 1 : self.start]
        return prefix if not prefix.strip(" \t") else ""


LITERAL_PREFIX = re.compile(r'\s*window\.(?P<key>logseq_db|logseq_state)\s*=\s*(?=")')
LITERAL_TAIL = re.compile(r"\s*;?\s*")
LITERAL_DECODER = json.JSONDecoder()


def read_legacy_literal(
    text: str, offset: int = 0
) -> tuple[re.Match[str], int, str] | None:
    prefix = LITERAL_PREFIX.match(text, offset)
    if not prefix:
        return None
    try:
        value, end = LITERAL_DECODER.raw_decode(text, prefix.end())
    except json.JSONDecodeError:
        return None
    assert isinstance(value, str)
    return prefix, end, value


class ScriptParser(HTMLParser):
    """Locate script spans in the source without serializing any HTML."""

    CDATA_CONTENT_ELEMENTS = (
        "script",
        "style",
        "textarea",
        "title",
        "xmp",
        "iframe",
        "noembed",
        "noframes",
        "noscript",
    )
    CLOSE_SCRIPT = re.compile(r"</script[\t\n\f\r ]*>", re.IGNORECASE)

    def __init__(self, html: str, *, recover_native_state: bool = False) -> None:
        super().__init__(convert_charrefs=False)
        self.source = html
        self.line_offsets = [0] + [match.end() for match in re.finditer("\n", html)]
        self.ids: Counter[str] = Counter()
        self.scripts: list[Script] = []
        self.pending: tuple[int, int, dict[str, str | None]] | None = None
        self.template_depth = 0
        if recover_native_state:
            self.feed_native_export(html)
        else:
            self.feed(html)
        self.close()
        if self.pending:
            raise PayloadError("script 元素未正确关闭，已停止。")

    def feed_native_export(self, html: str) -> None:
        """Recognize a native state literal before HTML can end its script."""
        cursor = 0
        for opening in re.finditer(r"<script>(?=\s*window\.logseq_state\s*=)", html):
            if opening.start() < cursor:
                continue
            self.feed(html[cursor : opening.end()])
            cursor = opening.end()
            # A textual match in a comment or another script is not an opening.
            if not self.pending or self.pending[0] != opening.start():
                continue
            literal = read_legacy_literal(html, cursor)
            if literal is None:
                continue
            prefix, last, _ = literal
            tail = LITERAL_TAIL.match(html, last)
            assert tail is not None
            if not self.CLOSE_SCRIPT.match(html, tail.end()):
                continue
            # Mask only the quoted string in the parser's view. Its length
            # and line breaks stay intact so all spans still index self.source.
            self.feed(
                html[cursor : prefix.end()]
                + html[prefix.end() : last].replace("<", " ")
            )
            cursor = last
        self.feed(html[cursor:])

    def source_offset(self) -> int:
        line, column = self.getpos()
        return self.line_offsets[line - 1] + column

    def remember_ids(self, attrs: list[tuple[str, str | None]]) -> None:
        for key, value in attrs:
            if key == "id" and value is not None:
                self.ids[value] += 1

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if not self.template_depth:
            self.remember_ids(attrs)
            if tag == "plaintext":
                raise PayloadError("不支持包含 plaintext 元素的导出。")
            if tag == "script":
                if len({key for key, _ in attrs}) != len(attrs):
                    raise PayloadError("script 元素包含重复属性。")
                start = self.source_offset()
                opening = self.get_starttag_text()
                assert opening is not None
                self.pending = start, start + len(opening), dict(attrs)
        if tag == "template":
            self.template_depth += 1

    def handle_startendtag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag == "template":
            self.handle_starttag(tag, attrs)
        elif not self.template_depth:
            if tag in ("script", "plaintext"):
                raise PayloadError("导出包含无效的自闭合 script 或 plaintext 元素。")
            self.remember_ids(attrs)

    def handle_endtag(self, tag: str) -> None:
        if tag == "template" and self.template_depth:
            self.template_depth -= 1
        elif tag == "script" and self.pending:
            start, body_start, attrs = self.pending
            body_end = self.source_offset()
            closing = self.CLOSE_SCRIPT.match(self.source, body_end)
            if not closing:
                raise PayloadError("script 元素未正确关闭，已停止。")
            self.scripts.append(
                Script(self.source, start, body_start, body_end, closing.end(), attrs)
            )
            self.pending = None


CLASSIC_TYPES = ("", "text/javascript", "application/javascript")


def script_type(block: Script) -> str:
    return (block.attrs.get("type") or "").strip().lower()


def bridge_code(key: str) -> str:
    return f'window.{key} = document.getElementById("{DATA_IDS[key]}").textContent;'


@dataclass
class Payload:
    key: str
    style: str
    script: Script
    first: int
    last: int
    loader: Script

    def start(self, _group: str = "value") -> int:
        return self.first

    def end(self, _group: str = "value") -> int:
        return self.last


def extract(
    html: str, key: str, *, require_available_id: bool = False
) -> tuple[Payload, str]:
    return extract_document(
        ScriptParser(html), key, require_available_id=require_available_id
    )


def extract_document(
    document: ScriptParser, key: str, *, require_available_id: bool = False
) -> tuple[Payload, str]:
    html = document.source
    blocks = document.scripts
    active = [
        block
        for block in blocks
        if script_type(block) in (*CLASSIC_TYPES, "module") and "src" not in block.attrs
    ]
    literals = []
    assignments = 0
    assignment = re.compile(r"\bwindow\." + re.escape(key) + r"\s*=")
    for block in active:
        body = block.body
        literal = read_legacy_literal(body)
        if literal is not None:
            prefix, last, value = literal
            if LITERAL_TAIL.fullmatch(body, last):
                # A public code example inside a known literal is data.
                if prefix["key"] == key:
                    assignments += 1
                    if script_type(block) in CLASSIC_TYPES:
                        literals.append((block, prefix.end(), last, value))
                continue
        assignments += len(assignment.findall(body))
    data = [block for block in blocks if block.attrs.get("id") == DATA_IDS[key]]
    if literals and require_available_id and document.ids[DATA_IDS[key]]:
        raise PayloadError("页面已存在同名 id，无法转换为数据块。")

    if assignments != 1 or len(literals) + len(data) != 1:
        raise PayloadError("嵌入数据缺失、重复或含未知赋值，已停止。")
    if literals:
        block, first, last, value = literals[0]
        offset = block.body_start
        return Payload(
            key,
            "literal",
            block,
            offset + first,
            offset + last,
            block,
        ), value
    block = data[0]
    bridges = [
        item
        for item in active
        if script_type(item) in CLASSIC_TYPES and item.body.strip() == bridge_code(key)
    ]
    if (
        block.attrs.get("type") != DATA_TYPES[key]
        or "src" in block.attrs
        or document.ids[DATA_IDS[key]] != 1
        or len(bridges) != 1
        or bridges[0].start < block.end
        or html[block.end : bridges[0].start].strip(" \t\n\r\f")
    ):
        raise PayloadError("展开数据的类型、加载器或顺序不符合预期。")
    value = block.body
    if key == "logseq_db":
        if ESCAPE_PREFIX in value:
            raise PayloadError("展开后的数据库包含未保护的 Logseq 实体标记，已停止。")
        load_json(value)
        value = TransitText(value)
    return Payload(
        key, "data", block, block.body_start, block.body_end, bridges[0]
    ), value


def data_body(key: str, value: str, indent: str = "") -> str:
    pretty = (
        pretty_database(unpack_database(value))
        if key == "logseq_db"
        else pretty_state(value)
    )
    return (
        "\n"
        + "\n".join(indent + "  " + line for line in pretty.split("\n"))
        + "\n"
        + indent
    )


def serialize_payload(payload: Payload, value: str) -> str:
    if payload.style == "data":
        return data_body(payload.key, value, payload.script.indent)
    return (
        json.dumps(value, ensure_ascii=True)
        .replace("<", r"\u003c")
        .replace(">", r"\u003e")
        .replace("&", r"\u0026")
    )


def data_markup(key: str, value: str, loader: Script) -> str:
    indent = loader.indent
    return (
        f'<script id="{DATA_IDS[key]}" type="{DATA_TYPES[key]}">'
        + data_body(key, value, indent)
        + "</script>\n"
        + indent
        + loader.opening
        + "\n"
        + indent
        + "  "
        + bridge_code(key)
        + "\n"
        + indent
        + loader.closing
    )


def fingerprint(info: os.stat_result) -> tuple[int, int, int, int, int]:
    return info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns


def read_export(root: Path) -> tuple[Path, bytes, os.stat_result]:
    if not root.is_dir() or not (root / "static").is_dir():
        raise CleanError("指定目录不是包含 static 的 wiki 导出目录。")
    if (root / "logseq").is_dir() and (
        (root / "pages").is_dir() or (root / "journals").is_dir()
    ):
        raise CleanError("指定目录看起来是 Logseq 原始图谱，拒绝处理。")
    target = root / "index.html"
    info = target.lstat()
    if not stat.S_ISREG(info.st_mode):
        raise CleanError("index.html 必须是普通文件，不能是符号链接。")
    with os.fdopen(
        os.open(target, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)), "rb"
    ) as handle:
        if fingerprint(os.fstat(handle.fileno())) != fingerprint(info):
            raise CleanError("读取前 index.html 已改变，请稍后重试。")
        data = handle.read()
        if fingerprint(os.fstat(handle.fileno())) != fingerprint(info):
            raise CleanError("读取期间 index.html 已改变，请稍后重试。")
    return target, data, info


@contextmanager
def export_lock(target: Path):
    """Serialize writes using a stable advisory lock outside the export.

    Editors/exporters that do not use this same lock can still change the file.
    Never unlink the lock: waiters must continue to share the same lock inode.
    """
    try:
        import fcntl
    except ImportError as error:
        raise CleanError(
            "写入需要支持 fcntl.flock 的系统；当前仍可使用只读预览。"
        ) from error
    # Use the same lock path even when processes have different TMPDIR settings.
    folder = Path("/tmp") / f"wiki-export-locks-{os.getuid()}"
    folder.mkdir(mode=0o700, exist_ok=True)
    info = folder.lstat()
    if (
        not stat.S_ISDIR(info.st_mode)
        or info.st_uid != os.getuid()
        or stat.S_IMODE(info.st_mode) != 0o700
    ):
        raise CleanError("临时锁目录的类型、所有者或权限不符合要求。")
    identity = os.fsencode(str(target.parent.resolve() / target.name))
    path = folder / (hashlib.sha256(identity).hexdigest() + ".lock")
    fd = os.open(
        path,
        os.O_RDWR
        | os.O_CREAT
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0),
        0o600,
    )
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.getuid()
            or stat.S_IMODE(info.st_mode) != 0o600
            or info.st_nlink != 1
        ):
            raise CleanError("临时锁文件的类型、所有者或权限不符合要求。")
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as error:
            if error.errno in (errno.EACCES, errno.EAGAIN, errno.EWOULDBLOCK):
                raise CleanError(
                    "另一个导出工具正在写入同一文件，请稍后重试。"
                ) from error
            raise
        yield
    finally:
        os.close(fd)


def write_export(
    target: Path, original: bytes, cleaned: bytes, info: os.stat_result
) -> None:
    """Check the export snapshot and replace it if its bytes changed."""

    def unchanged() -> None:
        _, current, current_info = read_export(target.parent)
        if current != original or fingerprint(current_info) != fingerprint(info):
            raise CleanError("index.html 已被其他程序改变，未覆盖文件。")

    with export_lock(target):
        unchanged()
        if cleaned == original:
            return
        descriptor, name = tempfile.mkstemp(
            prefix=".export-write-", suffix=".tmp", dir=target.parent
        )
        temporary = Path(name)
        try:
            with os.fdopen(descriptor, "wb") as handle:
                handle.write(cleaned)
                handle.flush()
                os.fchmod(handle.fileno(), stat.S_IMODE(info.st_mode))
                os.fsync(handle.fileno())
            unchanged()
            os.replace(temporary, target)
            try:
                directory = os.open(
                    target.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
                )
                try:
                    os.fsync(directory)
                finally:
                    os.close(directory)
            except OSError as error:
                raise WriteDurabilityError(
                    "index.html 已写入，但父目录同步失败，落盘持久性尚未确认。"
                ) from error
        finally:
            temporary.unlink(missing_ok=True)


def replace_regions(html: str, replacements: list[tuple[int, int, str]]) -> str:
    boundary = len(html)
    for start, end, replacement in sorted(replacements, reverse=True):
        if not 0 <= start <= end <= boundary:
            raise PayloadError("嵌入数据区域重叠，已停止。")
        html = html[:start] + replacement + html[end:]
        boundary = start
    return html


def outside_payloads(html: str, payloads: dict[str, tuple[Payload, str]]) -> str:
    return replace_regions(
        html,
        [
            (
                payload.script.start,
                payload.loader.end,
                payload.loader.opening + key + payload.loader.closing,
            )
            for key, (payload, _) in payloads.items()
        ],
    )


def format_html(html: str) -> tuple[str, dict[str, Any]]:
    document = ScriptParser(html, recover_native_state=True)
    before = {
        key: extract_document(document, key, require_available_id=True)
        for key in DATA_IDS
    }
    replacements = []
    for key, (payload, value) in before.items():
        if payload.style == "literal":
            replacements.append(
                (
                    payload.loader.start,
                    payload.loader.end,
                    data_markup(key, value, payload.loader),
                )
            )
        else:
            replacements.append(
                (payload.start(), payload.end(), serialize_payload(payload, value))
            )
    formatted = replace_regions(html, replacements)
    formatted_document = ScriptParser(formatted)
    after = {key: extract_document(formatted_document, key) for key in DATA_IDS}
    if unpack_database(before["logseq_db"][1]) != unpack_database(
        after["logseq_db"][1]
    ):
        raise PayloadError("格式化改变了隐藏数据库，已停止。")
    if edn_signature(before["logseq_state"][1]) != edn_signature(
        after["logseq_state"][1]
    ):
        raise PayloadError("格式化改变了配置数据，已停止。")
    if outside_payloads(html, before) != outside_payloads(formatted, after):
        raise PayloadError("格式化改变了嵌入数据区外的 HTML，已停止。")
    return formatted, {
        "changed": formatted != html,
        "database_preserved": True,
        "configuration_preserved": True,
        "other_html_preserved": True,
        "before_lines": len(html.splitlines()),
        "after_lines": len(formatted.splitlines()),
    }
