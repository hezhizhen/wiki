"""Clean the embedded database and configuration of a Logseq wiki export.

Only Logseq OG file-graph publishing exports are supported, with either legacy
strings or expanded data blocks. The default accepts explicitly public pages
and OG aliases with only page identity and linking metadata. Use
publication_mode="all" only for a verified all-public export. Pages marked
public:: false are always rejected.

Transit cache codes are expanded before filtering so removed records cannot
invalidate later references. Unknown attributes, unowned block data and
unsupported macro shapes are rejected. Public body text and system keyword
idents are kept; stale macro references and unused macro entities are removed.

The app state is rebuilt with an empty favorites list, the existing repository
key, light/dark theme and validated rendering settings. The cleaner
stops when dropping custom macro or query configuration may break public pages.

This is deliberately not a general-purpose secret scanner. Public page bodies,
attachments, bundles, and Git history are outside its scope.

Format references
https://github.com/logseq/logseq/blob/0.10.15/deps/publishing/src/logseq/publishing/html.cljs
https://github.com/logseq/logseq/blob/0.10.15/deps/db/src/logseq/db/rules.cljc
https://github.com/logseq/logseq/blob/0.10.15/deps/graph-parser/src/logseq/graph_parser/block.cljs
https://github.com/logseq/mldoc/blob/b3e06c0/lib/syntax/inline.ml
https://github.com/cognitect/transit-js/blob/master/src/com/cognitect/transit/caching.js
https://github.com/cognitect/transit-js/blob/master/src/com/cognitect/transit/impl/decoder.js
"""

from __future__ import annotations

import copy
import json
import re
from collections import defaultdict, deque
from dataclasses import dataclass
from typing import Any

from format import (
    CleanError,
    Collection,
    PayloadError,
    compact_state,
    edn_value,
    extract,
    load_json,
    parse_state,
    serialize_payload,
    state_mapping,
    state_semantics,
    transit_text,
    unpack_database,
)

MACRO_NAME = re.compile(r"[^}( \r\n]+")
MACRO_CALL = re.compile(r"\{\{\{([^}\r\n]+)\}\}\}|\{\{([^}\r\n]+)\}\}")
BACKTICKS = re.compile(r"`+")
HTML_CODE_START = r"<(?i:code|pre)(?=[ \t>])"
MACRO_OR_HTML = r"\{\{|" + HTML_CODE_START
MARKDOWN_INLINE_START = re.compile(r"`+|\[|" + MACRO_OR_HTML)
ORG_INLINE_START = re.compile(r"(?:^|(?<=[ \t\r\n\f]))[~=]|" + MACRO_OR_HTML)
HTML_CODE_OPEN = re.compile(
    r"""<(?P<tag>code|pre)(?=[ \t>])(?:[^"'<>\r\n]|"[^"\r\n]*"|'[^'\r\n]*')*(?<!/)>""",
    re.IGNORECASE,
)
BARE_URL_PREFIX = re.compile(r"[A-Za-z0-9]+://")
LINE_END = re.compile(r"[\r\n]")
CODE_TEXT = re.compile(r"[^\r\n]")
FENCE = r"`{3,}|~{3,}"
ORDERED_MARKER = r"[0-9]+\."
LIST_MARKER = rf"(?:[-+*]|{ORDERED_MARKER})[ \t]+"
BLOCK_PREFIX = rf"^(?P<indent>[ \t]*)(?P<item>{LIST_MARKER})?(?P<quotes>(?:>[ \t]*)*)"
QUERY_OPEN = r"#\+BEGIN_QUERY(?=[ \t\r\n]|$)[^\r\n]*\r?\n"
QUERY_CLOSE = r"#\+END_QUERY"
LITERAL_BLOCK = re.compile(
    BLOCK_PREFIX
    + rf"(?:(?P<html>{HTML_CODE_START})|(?P<fence>{FENCE})(?P<tail>[^\r\n]*)"
    + r"|#\+BEGIN_(?P<org>SRC|EXAMPLE)(?=[ \t\r\n]|$)"
    + rf"|(?P<query>{QUERY_OPEN}))",
    re.IGNORECASE | re.MULTILINE,
)
ADVANCED_QUERY = re.compile(BLOCK_PREFIX + QUERY_OPEN, re.IGNORECASE | re.MULTILINE)
QUERY_END = re.compile(
    r"^[ \t]*(?:>[ \t]*)*" + QUERY_CLOSE, re.IGNORECASE | re.MULTILINE
)
QUOTE_BREAK = r"(?:[-#](?=[ \t\r\n]|$)|id::[ \t])"
QUOTE_PARENT = re.compile(
    rf"^[ \t]*>[^\r\n]*(?:\r?\n(?![ \t]*(?:\r?$|(?:>[ \t]*)?{QUOTE_BREAK}))"
    r"[^\r\n]+)*\r?\n\Z",
    re.MULTILINE,
)
LIST_ITEM_END = re.compile(
    r"^(?:[^ \t]|[ \t]*(?:[-+*](?=[ \t\r\n]|$)|[+-]?[0-9]|\r?$))",
    re.MULTILINE,
)


def macro_argument(text: str) -> str:
    if text.startswith("[["):
        depth = 0
        for bracket in re.finditer(r"\[\[|\]\]", text):
            depth += 1 if bracket[0] == "[[" else -1
            if depth == 0:
                return text[: bracket.end()]
    if match := re.match(r'\(\([^)]+\)\)|"(?:\\.|[^"\\])+"', text):
        return match[0]
    return text.partition(",")[0]


def macro_identifier(call: str) -> str | None:
    """Build the same identifier as OG's macro->block."""
    name = MACRO_NAME.match(call)
    if name is None:
        return None
    arguments = []
    remaining = call[name.end() :].lstrip(" \t")
    while remaining:
        argument = macro_argument(remaining)
        if not argument:
            return None
        arguments.append(argument)
        remaining = remaining[len(argument) :].lstrip(" \t")
        if not remaining:
            break
        if not remaining.startswith(","):
            return None
        remaining = remaining[1:].lstrip(" \t")
        if not remaining:
            return None
    return name[0] + " " + " ".join(arguments)


def block_context(text: str, opening: re.Match[str], markdown: bool) -> tuple[int, int]:
    """Return the end of the enclosing item or quote and its quote depth."""
    limit = len(text)
    item = opening["item"]
    depth = opening["quotes"].count(">")
    if not (item or "").startswith("- ") and QUOTE_PARENT.search(
        text, 0, opening.start()
    ):
        # A lazy quote trims the indentation required to continue a list item.
        if item:
            return opening.end(), depth
        depth = depth or 1

    # Logseq treats Markdown dash bullets and top-level Org stars as headings.
    bullets = "+*" if markdown or opening["indent"] else "+-"
    in_list = item and (item[0].isdigit() or item[0] in bullets)
    if not item and opening["indent"]:
        parent_bullets = "+*" if markdown else "+*-"
        parent = re.compile(
            rf"^[ \t]*(?:[{parent_bullets}]|{ORDERED_MARKER})[ \t][^\r\n]*"
            r"(?:\r?\n[ \t][^\r\n]*)*\r?\n\Z",
            re.MULTILINE,
        )
        in_list = parent.search(text, 0, opening.start())
    if in_list and (boundary := LIST_ITEM_END.search(text, opening.end())):
        limit = boundary.start()

    if depth:
        boundary = re.compile(
            rf"^[ \t]*(?:>[ \t]*){{0,{depth}}}{QUOTE_BREAK}", re.MULTILINE
        ).search(text, opening.end(), limit)
        if boundary:
            limit = boundary.start()
    return limit, depth


def block_closing(
    text: str, opening: re.Match[str], marker: str, limit: int, depth: int
) -> re.Match[str] | None:
    prefix = rf"^[ \t]*(?:>[ \t]*){{0,{depth}}}"
    return re.compile(prefix + marker, re.IGNORECASE | re.MULTILINE).search(
        text, opening.end(), limit
    )


def html_code_end(text: str, start: int, limit: int) -> int | None:
    opening = HTML_CODE_OPEN.match(text, start, limit)
    if opening is None:
        return None
    tag = opening["tag"]
    closing = re.compile(rf"</{tag}>", re.IGNORECASE)
    depth = 1
    cursor = opening.end("tag")
    for match in closing.finditer(text, cursor, limit):
        # mldoc counts nested openers of the same tag before each close.
        body = text[cursor : match.start()]
        depth += body.count(f"<{tag}>") + body.count(f"<{tag} ") - 1
        if depth == 0:
            return match.end()
        cursor = match.end()
    return None


def outside_code(text: str, *, markdown: bool = True) -> str:
    """Mask complete code blocks in source order without changing offsets."""
    pieces = []
    cursor = 0
    processed_end = 0
    for opening in LITERAL_BLOCK.finditer(text):
        start = opening.start()
        if start < processed_end:
            continue
        limit, depth = block_context(text, opening, markdown)
        if opening["query"]:
            # EDN strings can contain fence markers. Leave the query for its reader.
            if depth <= 1 and (
                closing := block_closing(text, opening, QUERY_CLOSE, limit, depth)
            ):
                processed_end = line_limit(text, closing.end())
            continue
        if opening["html"]:
            end = html_code_end(text, opening.start("html"), limit)
        else:
            depth = opening["quotes"].count(">")
            if depth > 1:
                continue
            fence = opening["fence"]
            if fence and fence.startswith("`") and "`" in opening["tail"]:
                continue
            marker = rf"(?:{FENCE})" if fence else r"#\+END_" + opening["org"]
            closing = block_closing(text, opening, marker, limit, depth)
            end = line_limit(text, closing.end()) if closing else None
        if end is None:
            continue
        content = opening.end("quotes")
        pieces.extend((text[cursor:content], CODE_TEXT.sub(" ", text[content:end])))
        processed_end = cursor = end
    pieces.append(text[cursor:])
    return "".join(pieces)


def line_limit(text: str, start: int) -> int:
    line_end = LINE_END.search(text, start)
    return line_end.start() if line_end else len(text)


def code_span_end(text: str, opening: re.Match[str], limit: int) -> int | None:
    closing = re.compile(r"(?<!`)" + opening[0] + r"(?!`)").search(
        text, opening.end(), limit
    )
    return closing.end() if closing else None


def balanced_end(text: str, start: int, closing: str, limit: int) -> int | None:
    """Find the end of a Markdown link label or destination."""
    opening = text[start]
    depth = 1
    index = start + 1
    while index < limit:
        char = text[index]
        if (
            char == "\\"
            and index + 1 < limit
            and text[index + 1] in ("\\", opening, closing)
        ):
            index += 2
            continue
        if opening == "[" and (code := BACKTICKS.match(text, index, limit)):
            index = code_span_end(text, code, limit) or code.end()
            continue
        if char == opening:
            depth += 1
        elif char == closing:
            depth -= 1
            if depth == 0:
                return index + 1
        index += 1
    return None


def macro_invocations(text: str, *, markdown: bool = True) -> list[str]:
    """Scan visible text, skipping complete literal code and Markdown links."""
    result: list[str] = []
    index = 0
    inline_start = MARKDOWN_INLINE_START if markdown else ORG_INLINE_START
    while token := inline_start.search(text, index):
        start = token.start()
        index = token.end()
        before = start - 1
        while before >= 0 and text[before] == "\\":
            before -= 1
        if (start - before - 1) % 2:
            index = start + 1
            continue
        if token[0][0] == "`":
            index = code_span_end(text, token, line_limit(text, index)) or index
        elif token[0] in ("~", "="):
            closing = text.find(token[0], index, line_limit(text, index))
            if closing > index:
                index = closing + 1
        elif token[0][0] == "<":
            if not start or text[start - 1] in " \t\r\n\f":
                index = html_code_end(text, start, line_limit(text, index)) or index
        elif token[0] == "[":
            if text.startswith("[[", start):
                continue
            # A bare URL can consume the opening bracket before the link parser sees it.
            left = start
            while left and not text[left - 1].isspace():
                left -= 1
            if BARE_URL_PREFIX.match(text, left, start):
                continue
            limit = line_limit(text, index)
            label = balanced_end(text, start, "]", limit)
            if label is not None and label < limit and text[label] == "(":
                index = balanced_end(text, label, ")", limit) or index
        elif match := MACRO_CALL.match(text, start):
            identifier = macro_identifier(match[1] or match[2])
            if identifier is not None:
                result.append(identifier)
                index = match.end()
    return result


@dataclass
class PublicFeatures:
    invocations: list[str]
    advanced_queries: list[dict[str, Any] | None]
    journals: bool

    @property
    def macro_names(self) -> set[str]:
        return {text.split(" ", 1)[0] for text in self.invocations}


def public_features(
    texts: list[tuple[str, bool]], journals: bool = False
) -> PublicFeatures:
    calls = []
    queries = []
    for text, markdown in texts:
        visible = outside_code(text, markdown=markdown)
        pieces = []
        cursor = 0
        query_end = 0
        for opening in ADVANCED_QUERY.finditer(visible):
            if opening.start() < query_end:
                continue
            limit, depth = block_context(visible, opening, markdown)
            closing = block_closing(visible, opening, QUERY_CLOSE, limit, depth)
            literal = closing is not None and depth <= 1
            if closing is None:
                # Keep checking query settings when the source boundary is ambiguous.
                closing = QUERY_END.search(visible, opening.end())
                if closing is None:
                    continue
                depth = opening["quotes"].count(">")
            start, end = opening.end(), closing.start()
            query_end = line_limit(visible, closing.end())
            body = text[start:end]
            if depth:
                body = re.sub(rf"(?m)^(?:[ \t]*>[ \t]*){{1,{depth}}}", "", body)
            try:
                queries.append(state_mapping(parse_state(body, allow_comments=True)))
            except (PayloadError, RecursionError):
                queries.append(None)
                continue
            if not literal:
                continue
            # The query reader uses this EDN, so its literal strings aren't macro calls.
            pieces.extend(
                (visible[cursor:start], CODE_TEXT.sub(" ", visible[start:end]))
            )
            cursor = end
        pieces.append(visible[cursor:])
        calls.extend(macro_invocations("".join(pieces), markdown=markdown))
    return PublicFeatures(calls, queries, journals)


@dataclass
class StateContext:
    root: dict[str, Any]
    repo_key: str
    config: dict[str, Any]
    macro_names: set[str]


def repo_configuration(root: dict[str, Any]) -> tuple[str, Collection]:
    if ":config" not in root:
        raise PayloadError("发布 state 缺少 :config，无法确定仓库键。")
    repos = state_mapping(root[":config"])
    if len(repos) != 1:
        raise PayloadError("只支持包含单个发布仓库配置的 state。")
    repo_key, configuration = next(iter(repos.items()))
    if not repo_key.startswith('"'):
        raise PayloadError("发布仓库键必须是字符串。")
    repo = load_json(repo_key)
    if not repo.strip() or len(repo) > 128 or re.search(r"[/\\:@\x00-\x1f]", repo):
        raise PayloadError("发布仓库键包含路径或不支持的内容，拒绝公开。")
    if not isinstance(configuration, Collection) or configuration.opener != "{":
        raise PayloadError("发布仓库配置必须是 EDN 映射。")
    return repo_key, configuration


def state_context(payload: str) -> StateContext:
    root = state_mapping(parse_state(payload))
    repo_key, configuration = repo_configuration(root)
    config = state_mapping(configuration)
    definitions_node = config.get(":macros", Collection("{", []))
    definitions = {} if definitions_node == "nil" else state_mapping(definitions_node)
    names = set()
    for key in definitions:
        if key.startswith('"'):
            names.add(load_json(key))
        elif key.startswith(":"):
            names.add(key[1:])
        else:
            raise PayloadError("自定义宏名称必须是字符串或关键字。")
    return StateContext(root, repo_key, config, names)


RENDER_FIELDS = (
    ":journal/page-title-format",
    ":property-pages/enabled?",
    ":file/name-format",
    ":meta/version",
    ":ui/show-brackets?",
    ":block-hidden-properties",
)
DATE_PATTERN = re.compile(r"[yMdoE ,./_年月日-]{1,128}")
KEYWORD_PART = r"(?![.+-]\d)(?:[^\W\d]|[.*+!?$%&=<>-])[\w.*+!?$%&=<>:#-]*"
PROPERTY_KEYWORD = re.compile(rf":{KEYWORD_PART}(?:/{KEYWORD_PART})?")


def normalize_hidden_properties(value: Any) -> Collection:
    if value == "nil":
        return Collection("#{", [])
    if (
        not isinstance(value, Collection)
        or value.opener not in ("#{", "[", "(")
        or any(
            not isinstance(name, str) or not PROPERTY_KEYWORD.fullmatch(name)
            for name in value.children
        )
    ):
        raise PayloadError("隐藏属性配置必须是由属性关键字组成的集合、向量或列表。")
    names = list(dict.fromkeys(value.children))
    if value.opener == "#{":
        if len(names) != len(value.children):
            raise PayloadError("隐藏属性集合包含重复关键字。")
        return value
    return Collection("#{", names)


def has_entries(value: Any) -> bool:
    return (
        value is not None
        and value != "nil"
        and (not isinstance(value, Collection) or bool(value.children))
    )


def query_config_dependency(
    config: dict[str, Any], features: PublicFeatures
) -> str | None:
    """Find a query setting the published content may still read."""
    queries = [query for query in features.advanced_queries if query is not None]
    unresolved = len(queries) != len(features.advanced_queries)
    for key, option in (
        (":query/views", ":view"),
        (":query/result-transforms", ":result-transform"),
    ):
        definitions = config.get(key)
        if not has_entries(definitions):
            continue
        if unresolved:
            return key
        names = {
            name
            for query in queries
            if isinstance(name := query.get(option), str) and name.startswith(":")
        }
        if names:
            try:
                values = state_mapping(definitions)
            except PayloadError:
                return key
            if any(values.get(name) not in (None, "nil", "false") for name in names):
                return key

    key = ":default-queries"
    defaults = config.get(key)
    titles = {edn_value(query.get(":title", "nil")) for query in queries}
    if "query" in features.macro_names:
        titles.add(edn_value("nil"))
    if not has_entries(defaults) or not (titles or features.journals or unresolved):
        return None
    try:
        journals = state_mapping(defaults).get(":journals")
        if not has_entries(journals):
            return None
        if (
            features.journals
            or unresolved
            or not isinstance(journals, Collection)
            or journals.opener not in ("[", "(")
        ):
            return key
        if any(
            edn_value(state_mapping(query).get(":title", "nil")) in titles
            for query in journals.children
        ):
            return key
    except PayloadError:
        return key
    return None


def clean_configuration(
    context: StateContext, features: PublicFeatures
) -> tuple[str, list[str]]:
    if features.macro_names & context.macro_names:
        raise PayloadError("公开内容使用了自定义宏定义，不能在删除配置后保证渲染不变。")
    if key := query_config_dependency(context.config, features):
        raise PayloadError("公开查询或日志可能依赖 " + key + "，需要先审核其公开配置。")
    kept: list[Any] = [":favorites", Collection("[", [])]
    preserved = []
    for key in RENDER_FIELDS:
        if key not in context.config:
            continue
        value = context.config[key]
        if key == ":journal/page-title-format":
            if not isinstance(value, str) or not value.startswith('"'):
                raise PayloadError("日志标题格式必须是字符串。")
            pattern = load_json(value)
            if not DATE_PATTERN.fullmatch(pattern) or not re.search("[yMdE]", pattern):
                raise PayloadError("日志标题格式不在可安全保留的日期格式范围内。")
        elif key == ":property-pages/enabled?" and value not in ("true", "false"):
            raise PayloadError("属性页面开关必须是布尔值。")
        elif key == ":file/name-format" and value not in (":legacy", ":triple-lowbar"):
            raise PayloadError("文件名格式不受支持。")
        elif key == ":meta/version" and (
            not isinstance(value, str) or not re.fullmatch(r"0|[1-9]\d{0,8}", value)
        ):
            raise PayloadError("配置版本标记不受支持。")
        elif key == ":block-hidden-properties" and value != "nil":
            value = normalize_hidden_properties(value)
        elif key == ":ui/show-brackets?" and value not in ("true", "false", "nil"):
            raise PayloadError("页面引用括号开关必须是布尔值或 nil。")
        kept.extend((key, value))
        preserved.append(key)
    state: list[Any] = []
    if ":ui/theme" in context.root:
        value = context.root[":ui/theme"]
        theme = (
            load_json(value)
            if isinstance(value, str) and value.startswith('"')
            else None
        )
        if theme not in ("dark", "light"):
            raise PayloadError("主题不是支持的明/暗主题，拒绝静默丢弃。")
        state.extend((":ui/theme", json.dumps(theme)))
    state.extend(
        (":config", Collection("{", [context.repo_key, Collection("{", kept)]))
    )
    return compact_state(Collection("{", state)), preserved


SUPPORTED_TAGS = {"~#datascript/DB", "~#datascript/Datom", "~#list", "~#set"}


class TransitCacheExpander:
    """Expand compact Transit cache tokens while preserving the wire types.

    The cache uses 44 base digits, starting at character 48, and wraps after
    1936 entries. Strings in map-key position and ~:, ~$ or ~# tokens are cached
    when their JavaScript UTF-16 length exceeds three. No Transit code is run.
    """

    def __init__(self) -> None:
        self.cache: list[str | None] = [None] * (44 * 44)
        self.next_index = 0

    def lookup(self, token: str) -> str:
        if len(token) not in (2, 3):
            raise CleanError("Transit 缓存引用格式异常，已停止。")
        digits = [ord(char) - 48 for char in token[1:]]
        if any(not 0 <= digit < 44 for digit in digits):
            raise CleanError("Transit 缓存引用超出范围，已停止。")
        index = digits[0] if len(digits) == 1 else digits[0] * 44 + digits[1]
        value = self.cache[index]
        if value is None:
            raise CleanError("Transit 数据包含未定义的缓存引用，已停止。")
        return value

    def string(self, token: str, as_key: bool) -> str:
        length = len(token.encode("utf-16-le", errors="surrogatepass")) // 2
        if length > 3 and (as_key or token.startswith(("~:", "~$", "~#"))):
            if self.next_index == len(self.cache):
                self.next_index = 0
            self.cache[self.next_index] = token
            self.next_index += 1
            return token
        if token.startswith("^") and token != "^ ":
            return self.lookup(token)
        return token

    def expand(self, node: Any, as_key: bool = False, tag_rep: bool = False) -> Any:
        if isinstance(node, str):
            return self.string(node, as_key)
        if isinstance(node, dict):
            raise CleanError("仅支持 Logseq 的紧凑 Transit 数组格式，已停止。")
        if not isinstance(node, list):
            return node
        if node and node[0] == "^ ":
            if len(node) % 2 != 1:
                raise CleanError("Transit 映射结构异常，已停止。")
            result: list[Any] = ["^ "]
            for index in range(1, len(node), 2):
                result.append(self.expand(node[index], as_key=True))
                result.append(self.expand(node[index + 1]))
            return result
        if not tag_rep and len(node) == 2 and isinstance(node[0], str):
            first = node[0]
            if first.startswith("^") and first != "^ ":
                first = self.lookup(first)
            if first.startswith("~#"):
                if first not in SUPPORTED_TAGS:
                    raise CleanError("导出包含尚未支持的 Transit 类型，已停止。")
                tag = self.expand(node[0])
                return [tag, self.expand(node[1], as_key=as_key, tag_rep=True)]
        return [self.expand(value, as_key=as_key) for value in node]


def transit_map(node: Any) -> dict[str, Any]:
    if not isinstance(node, list) or not node or node[0] != "^ " or len(node) % 2 != 1:
        raise CleanError("数据库映射格式与预期不符，已停止。")
    result: dict[str, Any] = {}
    for index in range(1, len(node), 2):
        key = node[index]
        if not isinstance(key, str) or key in result:
            raise CleanError("数据库映射的键格式异常，已停止。")
        result[key] = node[index + 1]
    return result


def plain_string(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    if value.startswith(("~~", "~^", "~`")):
        return value[1:]
    return None if value.startswith("~") else value


def entity_id(value: Any) -> bool:
    return type(value) is int and value > 0


def database_parts(wire: Any) -> tuple[dict[str, Any], list[Any]]:
    if not isinstance(wire, list) or len(wire) != 2 or wire[0] != "~#datascript/DB":
        raise CleanError("未找到预期的 datascript/DB 数据库，已停止。")
    fields = transit_map(wire[1])
    if set(fields) != {"~:schema", "~:datoms"}:
        raise CleanError("数据库字段发生变化，需要先检查新的导出格式。")
    sequence = fields["~:datoms"]
    if not isinstance(sequence, list) or len(sequence) != 2 or sequence[0] != "~#list":
        raise CleanError("数据库 datoms 格式与预期不符，已停止。")
    datoms = sequence[1]
    if not isinstance(datoms, list):
        raise CleanError("数据库 datoms 不是列表，已停止。")
    for datom in datoms:
        if (
            not isinstance(datom, list)
            or len(datom) != 2
            or datom[0] != "~#datascript/Datom"
        ):
            raise CleanError("数据库记录格式异常，已停止。")
        record = datom[1]
        if not isinstance(record, list) or len(record) not in (4, 5):
            raise CleanError("数据库记录长度异常，已停止。")
        if (
            not entity_id(record[0])
            or not isinstance(record[1], str)
            or not record[1].startswith("~:")
        ):
            raise CleanError("数据库记录的实体或属性格式异常，已停止。")
    return fields, datoms


KNOWN_REFS = {
    "~:block/alias",
    "~:block/file",
    "~:block/left",
    "~:block/macros",
    "~:block/namespace",
    "~:block/page",
    "~:block/parent",
    "~:block/path-refs",
    "~:block/refs",
    "~:block/tags",
}
KNOWN_SCHEMA = KNOWN_REFS | {
    "~:schema/version",
    "~:ast/version",
    "~:db/type",
    "~:db/ident",
    "~:recent/pages",
    "~:block/type",
    "~:block/uuid",
    "~:block/collapsed?",
    "~:block/format",
    "~:block/content",
    "~:block/marker",
    "~:block/priority",
    "~:block/properties",
    "~:block/properties-order",
    "~:block/properties-text-values",
    "~:block/pre-block?",
    "~:block/scheduled",
    "~:block/deadline",
    "~:block/repeated?",
    "~:block/created-at",
    "~:block/updated-at",
    "~:block/name",
    "~:block/original-name",
    "~:block/journal?",
    "~:block/journal-day",
    "~:file/path",
    "~:file/content",
    "~:file/handle",
}
KNOWN_DATA = (
    KNOWN_SCHEMA
    - {
        "~:block/file",
        "~:file/path",
        "~:file/content",
        "~:file/handle",
        "~:recent/pages",
    }
) | {
    "~:block/invalid-properties",
    "~:block/warning",
}
# A generated alias can also be a referenced page or a namespace placeholder.
ALIAS_PAGE_FIELDS = {
    "~:block/name",
    "~:block/original-name",
    "~:block/alias",
    "~:block/uuid",
    "~:block/namespace",
    "~:block/format",
    "~:block/created-at",
    "~:block/updated-at",
    "~:block/journal?",
    "~:block/journal-day",
}


def rendered_strings(value: Any) -> list[str]:
    text = plain_string(value)
    if text is not None:
        return [text]
    if not isinstance(value, list):
        return []
    if value and value[0] == "^ ":
        return [text for child in value[2::2] for text in rendered_strings(child)]
    return [text for child in value for text in rendered_strings(child)]


def public_data(
    entities: dict[int, dict[str, list[Any]]],
    publication_mode: str = "explicit",
) -> tuple[set[int], set[int], list[tuple[str, bool]], bool]:
    if publication_mode not in ("explicit", "all"):
        raise CleanError("未知公开性判断模式。")
    pages = {eid for eid, attrs in entities.items() if "~:block/name" in attrs}
    if not pages:
        raise CleanError("没有发现页面，已停止。")
    flags = {}
    forward: dict[int, set[int]] = defaultdict(set)
    reverse: dict[int, set[int]] = defaultdict(set)
    for eid in pages:
        values = entities[eid].get("~:block/properties", [])
        if len(values) > 1:
            raise CleanError("页面属性重复，已停止。")
        properties = transit_map(values[0]) if values else {}
        flag = properties.get("~:public")
        if flag is False:
            raise CleanError("导出包含 public:: false 的页面，拒绝处理。")
        if "~:public" in properties and flag is not True:
            raise CleanError("页面 public 属性不是布尔值，已停止。")
        flags[eid] = flag
        for target in entities[eid].get("~:block/alias", []):
            if target in pages:
                forward[eid].add(target)
                reverse[target].add(eid)
    explicit = {eid for eid in pages if flags[eid] is True}
    content_pages = pages if publication_mode == "all" else explicit
    allowed = set(content_pages)
    # Match OG's direct/reverse and two directed-hop alias rules. Do not trust
    # an arbitrary undirected alias component or infer all-public from config.
    if publication_mode == "explicit":
        for eid in explicit:
            allowed.update(forward[eid] | reverse[eid])
            for middle in forward[eid]:
                allowed.update(forward[middle])
            for middle in reverse[eid]:
                allowed.update(reverse[middle])
    if allowed != pages:
        raise CleanError("默认只接受 public:: true 页面及其纯别名。")
    for eid in allowed - content_pages:
        if not entities[eid].keys() <= ALIAS_PAGE_FIELDS:
            raise CleanError("未标记 public:: true 的别名页包含独立页面数据，已停止。")
    owned: set[int] = set()
    texts: list[tuple[str, bool]] = []
    for eid, attrs in entities.items():
        owners = attrs.get("~:block/page", [])
        markdown = attrs.get("~:block/format") != ["~:org"]
        if owners or "~:block/content" in attrs:
            if len(owners) != 1 or not entity_id(owners[0]) or owners[0] not in allowed:
                raise CleanError("发现不属于公开页面的块，已停止。")
            if owners[0] not in content_pages:
                raise CleanError(
                    "未标记 public:: true 的别名页包含正文或块数据，已停止。"
                )
            owned.add(eid)
        if "~:block/content" in attrs:
            values = attrs["~:block/content"]
            text = plain_string(values[0]) if len(values) == 1 else None
            if text is None:
                raise CleanError("公开正文格式异常，已停止。")
            texts.append((text, markdown))
        if eid in allowed or eid in owned:
            for attr in ("~:block/properties", "~:block/properties-text-values"):
                for value in attrs.get(attr, []):
                    texts.extend((text, markdown) for text in rendered_strings(value))
    journals = any(
        entities[eid].get("~:block/journal?") == [True]
        or "~:block/journal-day" in entities[eid]
        for eid in allowed
    )
    return allowed, owned, texts, journals


def macro_entities(entities: dict[int, dict[str, list[Any]]]) -> dict[int, str]:
    result = {}
    for eid, attrs in entities.items():
        idents = attrs.get("~:db/ident", [])
        if len(idents) > 1:
            raise CleanError("实体包含重复标识，已停止。")
        name = plain_string(idents[0]) if idents else None
        kinds = attrs.get("~:block/type", [])
        macro_block = any(plain_string(value) in ("macro", "macros") for value in kinds)
        if macro_block and name is None:
            raise CleanError(
                "不支持 DB graph 的 macro block；只接受 OG file-graph 宏标识。"
            )
        if name is None:
            continue
        # OG's publisher keeps :db/ident even when it removes the macro's
        # :block/type and :block/properties. The name may be a private macro.
        head, separator, arguments = name.partition(" ")
        if (
            not separator
            or not MACRO_NAME.fullmatch(head)
            or re.search(r"[}\r\n]", arguments)
            or not set(attrs) <= {"~:db/ident", "~:block/type", "~:block/properties"}
            or (kinds and (len(kinds) != 1 or not macro_block))
        ):
            raise CleanError("字符串 db/ident 不符合受支持的 file-graph 宏实体形状。")
        properties = attrs.get("~:block/properties", [])
        if properties:
            if len(properties) != 1:
                raise CleanError("宏属性重复。")
            props = transit_map(properties[0])
            if set(props) != {"~:logseq.macro-name", "~:logseq.macro-arguments"}:
                raise CleanError("宏属性不符合受支持的 file-graph 形状。")
            args = props["~:logseq.macro-arguments"]
            if plain_string(props["~:logseq.macro-name"]) != head or not isinstance(
                args, list
            ):
                raise CleanError("宏标识和宏属性不一致，已停止。")
            arg_texts = [plain_string(arg) for arg in args]
            if (
                any(arg is None for arg in arg_texts)
                or head + " " + " ".join(arg for arg in arg_texts if arg is not None)
                != name
            ):
                raise CleanError("宏标识和宏属性不一致，已停止。")
        result[eid] = name
    return result


def clean_database(
    payload: str,
    publication_mode: str = "explicit",
) -> tuple[str, dict[str, Any], PublicFeatures]:
    original = TransitCacheExpander().expand(unpack_database(payload))
    fields, datoms = database_parts(original)
    schema = transit_map(fields["~:schema"])
    used = {datom[1][1] for datom in datoms}
    if "~:block/title" in used or "~:block/title" in schema:
        raise CleanError(
            "不支持 DB graph 或混合格式的 block/title；只接受 file-graph 导出。"
        )
    if not set(schema) <= KNOWN_SCHEMA or not used <= KNOWN_DATA:
        raise CleanError("导出包含未知或非发布属性；请先审核新的 file-graph 格式。")
    references = {
        attr
        for attr, options in schema.items()
        if transit_map(options).get("~:db/valueType") == "~:db.type/ref"
    }
    if references - KNOWN_REFS or (used & KNOWN_REFS) - references:
        raise CleanError("引用属性声明与受支持的 file-graph schema 不一致。")
    entities: dict[int, dict[str, list[Any]]] = defaultdict(lambda: defaultdict(list))
    for datom in datoms:
        eid, attr, value = datom[1][:3]
        entities[eid][attr].append(value)
        if attr in references and not entity_id(value):
            raise CleanError("数据库引用不是预期的实体编号，已停止。")
    pages, owned, texts, journals = public_data(entities, publication_mode)
    features = public_features(texts, journals)
    public_names = features.macro_names
    macros = macro_entities(entities)
    public_entities = pages | owned | macros.keys()
    for eid, attrs in entities.items():
        if eid not in public_entities and any(
            attr.startswith("~:block/") for attr in attrs
        ):
            raise CleanError("发现没有公开页面归属的块元数据，已停止。")
    identifiers = set(features.invocations)
    invoked = {eid for eid, name in macros.items() if name in identifiers}
    roots = pages | owned | invoked
    edges: dict[int, set[int]] = defaultdict(set)
    for datom in datoms:
        eid, attr, value = datom[1][:3]
        if attr not in references:
            continue
        if attr == "~:block/macros":
            if value not in macros:
                raise CleanError("block/macros 指向未知宏实体。")
            if value not in invoked:
                if macros[value].partition(" ")[0] in public_names:
                    raise CleanError(
                        "公开内容有同名宏，但参数与数据库引用不一致，无法确认引用已失效。"
                    )
                continue  # Remove stale macro edges instead of retaining unused identifiers.
        edges[eid].add(value)
    reachable = set(roots)
    pending = deque(roots)
    while pending:
        for target in edges.get(pending.popleft(), ()):
            if target not in reachable:
                reachable.add(target)
                pending.append(target)
    removed = set(macros) - reachable
    stale_edges = {
        index
        for index, datom in enumerate(datoms)
        if datom[1][1] == "~:block/macros" and datom[1][2] in removed
    }
    kept_datoms = [
        datom
        for index, datom in enumerate(datoms)
        if datom[1][0] not in removed and index not in stale_edges
    ]
    if any(
        record[1] in references and record[2] in removed for _, record in kept_datoms
    ):
        raise CleanError("保留数据仍引用待删除宏，已停止。")
    cleaned = copy.deepcopy(original)
    _, cleaned_datoms = database_parts(cleaned)
    cleaned_datoms[:] = kept_datoms
    serialized = transit_text(cleaned)
    if TransitCacheExpander().expand(unpack_database(serialized)) != cleaned:
        raise CleanError("清洗后数据库校验失败，已停止。")
    return (
        serialized,
        {
            "format": "og-file-graph",
            "publication_mode": publication_mode,
            "public_pages": len(pages),
            "content_blocks": sum("~:block/content" in entities[eid] for eid in owned),
            "removed_macro_entities": len(removed),
            "retained_macro_entities": len(macros) - len(removed),
            "removed_datoms": len(datoms) - len(kept_datoms),
            "removed_stale_macro_references": len(stale_edges),
            "public_macro_invocations": len(features.invocations),
        },
        features,
    )


def clean_state(payload: str, features: PublicFeatures | None = None) -> str:
    return clean_configuration(
        state_context(payload), features or PublicFeatures([], [], False)
    )[0]


def clean_html(
    html: str, publication_mode: str = "explicit"
) -> tuple[str, dict[str, Any]]:
    db_match, db_payload = extract(html, "logseq_db")
    state_match, state_payload = extract(html, "logseq_state")
    context = state_context(state_payload)
    cleaned_db, report, features = clean_database(db_payload, publication_mode)
    cleaned_state, preserved = clean_configuration(context, features)
    state_changed = state_semantics(cleaned_state) != state_semantics(state_payload)
    database_changed = unpack_database(cleaned_db) != TransitCacheExpander().expand(
        unpack_database(db_payload)
    )
    replacements = []
    if database_changed:
        replacements.append(
            (db_match.start(), db_match.end(), serialize_payload(db_match, cleaned_db))
        )
    if state_changed:
        replacements.append(
            (
                state_match.start(),
                state_match.end(),
                serialize_payload(state_match, cleaned_state),
            )
        )
    cleaned = html
    for start, end, value in sorted(replacements, reverse=True):
        cleaned = cleaned[:start] + value + cleaned[end:]
    actual_db = TransitCacheExpander().expand(
        unpack_database(extract(cleaned, "logseq_db")[1])
    )
    if actual_db != unpack_database(cleaned_db) or state_semantics(
        extract(cleaned, "logseq_state")[1]
    ) != state_semantics(cleaned_state):
        raise CleanError("清洗后的嵌入数据校验失败，已停止。")
    return cleaned, {
        **report,
        "preserved_render_config": preserved,
        "state_reset": state_changed,
        "changed": cleaned != html,
    }
