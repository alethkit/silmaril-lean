// Pure functions of the compiler explorer's view: no DOM. Tested by tests/view.test.mjs.

/** Byte offset [start, end) of each line of a text (as UTF-8 bytes), lines numbered from 1. */
export function lineOffsets(text) {
  const enc = new TextEncoder();
  const out = [];
  let pos = 0;
  for (const line of text.split("\n")) {
    const n = enc.encode(line).length;
    out.push([pos, pos + n]);
    pos += n + 1;
  }
  if (text.endsWith("\n")) out.pop();
  return out;
}

const overlaps = (a0, a1, b0, b1) => (a0 < b1 && b0 < a1) || (a0 === a1 && b0 <= a0 && a0 < b1);

/** The 1-based display lines a fragment covers. `lines` are the byte ranges of the displayed text;
 * `targetMap` (for the `text-offset` space) lists [offLo, offHi, byteStart, byteEnd] per listing line. */
export function fragmentLines(fragment, lines, targetMap) {
  const out = new Set();
  for (const [lo, hi] of fragment.ranges) {
    if (fragment.space === "bytes") {
      lines.forEach(([s, e], i) => { if (overlaps(lo, hi, s, e)) out.add(i + 1); });
    } else if (fragment.space === "text-offset") {
      for (const [o0, o1, s] of targetMap || []) {
        if (overlaps(lo, hi, o0, o1)) {
          const i = lines.findIndex(([ls]) => ls === s);
          if (i >= 0) out.add(i + 1);
        }
      }
    }
  }
  return [...out].sort((a, b) => a - b);
}

/** Index the edges of one kind: for each side, display line -> edge ids, and edge -> lines.
 * The relation is many-to-many: a line can lie in several edges and an edge spans several lines
 * (on either side, possibly not contiguous). */
export function indexEdges(problem, kind, srcLines, tgtLines) {
  const map = problem.view.target_map;
  const lines = { source: srcLines, target: tgtLines };
  const byLine = { source: new Map(), target: new Map() };
  const edgeLines = new Map();
  for (const e of problem.edges) {
    if (e.kind !== kind) continue;
    const el = { source: new Set(), target: new Set() };
    for (const side of ["source", "target"]) {
      for (const fid of e[side]) {
        const f = problem.fragments[fid];
        if (!f) continue;
        for (const n of fragmentLines(f, lines[side], side === "target" ? map : null)) {
          el[side].add(n);
          if (!byLine[side].has(n)) byLine[side].set(n, []);
          byLine[side].get(n).push(e.id);
        }
      }
    }
    edgeLines.set(e.id, { source: [...el.source].sort((a, b) => a - b), target: [...el.target].sort((a, b) => a - b) });
  }
  return { byLine, edgeLines };
}

/** The obligations attached to an edge (its segment and its C-to-Core point). */
export function edgeObligations(problem, edgeId) {
  return problem.obligations.filter((o) => o.edge === edgeId);
}

/** What a status badge says. Only the server's `proved` is ever shown as proved. */
export function badge(status) {
  const known = {
    proved: ["proved", "a theorem of exactly this statement, checked when Lean built it; read back by the exporter this database ran"],
    claimed: ["claimed", "an exporter result handed in as a file, not run by this database"],
    open: ["open", "stated in Lean, neither proved nor disproved: unknown"],
    unchecked: ["unchecked", "a proof is named but no checked evidence is recorded"],
    rejected: ["rejected", "the named proof does not prove this statement"],
    stale: ["stale", "proved only for another version of these artifacts"],
    refuted: ["disproved", "a theorem of the statement's negation, checked by Lean's kernel"],
    unbound: ["unbound", "a theorem proves it, but the Lean function is not shown to be the target's code"],
    unsupported: ["unsupported", "not stated: no model covers it"],
    passed: ["test passed", "an execution test, not a proof"],
    failed: ["test failed", "an execution test failed"],
  };
  const [label, title] = known[status] || ["unknown", "no status recorded"];
  return { cls: `st-${known[status] ? status : "unknown"}`, label, title };
}

/** Lines of a side not covered by any edge of a kind (optimized away, generated, unattributed). */
export function uncovered(index, side, count, isCode) {
  const out = [];
  for (let n = 1; n <= count; n++) if (isCode(n) && !index.byLine[side].has(n)) out.push(n);
  return out;
}

// ---------- syntax highlighting: tokens, never HTML ----------
// A highlighter returns, per line, a list of [text, class] tokens whose texts concatenate to the
// line exactly; the page inserts each token with textContent, so no text is ever parsed as HTML.

const C_KEYWORDS = new Set(("auto break case char const continue default do double else enum extern float for goto if " +
  "inline int long register restrict return short signed sizeof static struct switch typedef union unsigned void " +
  "volatile while _Bool _Complex _Atomic _Static_assert _Noreturn _Alignas _Alignof _Generic _Thread_local").split(" "));

/** The language of an artifact by its media type. */
export function langOf(media) {
  if (media === "text/x-c") return "c";
  if (media === "text/x-asm" || media === "text/x-objdump") return "asm";
  if (media === "text/x-lisp") return "sexp";
  return "plain";
}

function scan(line, rules) {
  const out = [];
  let i = 0;
  while (i < line.length) {
    let hit = null;
    for (const [re, cls] of rules) {
      re.lastIndex = i;
      const m = re.exec(line);
      if (m && m.index === i && m[0].length) { hit = [m[0], typeof cls === "function" ? cls(m[0]) : cls]; break; }
    }
    if (!hit) hit = [line[i], ""];
    if (out.length && out[out.length - 1][1] === hit[1]) out[out.length - 1][0] += hit[0];
    else out.push(hit);
    i += hit[0].length;
  }
  return out;
}

const C_RULES = [
  [/\/\/.*/y, "tok-comment"], [/\/\*.*?(\*\/|$)/y, "tok-comment"],
  [/"(\\.|[^"\\])*"?/y, "tok-string"], [/'(\\.|[^'\\])*'?/y, "tok-string"],
  [/^\s*#\s*\w+/y, "tok-preproc"],
  [/0[xX][0-9a-fA-F]+[uUlL]*|\d+(\.\d+)?([eE][+-]?\d+)?[uUlLfF]*/y, "tok-number"],
  [/[A-Za-z_]\w*/y, (w) => (C_KEYWORDS.has(w) ? "tok-keyword" : "")],
];
const ASM_RULES = [
  [/#.*/y, "tok-comment"], [/^\s*[0-9a-f]+:(?=\t)/y, "tok-address"], [/^\s*[.\w$]+:/y, "tok-label"],
  [/(?<=\t)([0-9a-f]{2} )+(?=\s*\t)/y, "tok-bytes"],
  [/\.[A-Za-z_][\w.]*/y, "tok-directive"], [/%[a-z0-9]+/y, "tok-register"],
  [/\$?-?0x[0-9a-fA-F]+|\$?-?\d+/y, "tok-number"], [/"(\\.|[^"\\])*"?/y, "tok-string"],
  [/<[^>\n]*>/y, "tok-label"],
];
const SEXP_RULES = [
  [/"(\\.|[^"\\])*"?/y, "tok-string"], [/\$[A-Za-z_]+/y, "tok-keyword"], [/-?\d+/y, "tok-number"],
  [/[()]/y, "tok-punct"],
];

/** Tokens of one line of a language. */
export function highlightLine(line, lang) {
  if (lang === "c") return scan(line, C_RULES);
  if (lang === "asm") return scan(line, ASM_RULES);
  if (lang === "sexp") return scan(line, SEXP_RULES);
  return [[line, ""]];
}

/** Tokens of every line of a text: C block comments carry over lines. */
export function highlightText(text, lang) {
  const out = [];
  let open = false;
  for (const line of text.split("\n")) {
    if (lang === "c" && open) {
      const end = line.indexOf("*/");
      if (end < 0) { out.push([[line, "tok-comment"]]); continue; }
      const rest = highlightLine(line.slice(end + 2), lang);
      out.push([[line.slice(0, end + 2), "tok-comment"], ...rest.filter((t) => t[0].length)]);
      open = opensComment(line.slice(end + 2));
      continue;
    }
    out.push(highlightLine(line, lang));
    open = lang === "c" && opensComment(line);
  }
  return out;
}

// Whether a line of C leaves a block comment open (strings and line comments respected).
function opensComment(line) {
  const toks = highlightLine(line, "c");
  const last = toks[toks.length - 1];
  return !!last && last[1] === "tok-comment" && last[0].startsWith("/*") && !last[0].endsWith("*/");
}
