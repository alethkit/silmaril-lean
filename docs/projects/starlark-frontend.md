# Starlark source frontend

This frontend reads a scalar subset of the [pinned Starlark core
profile](starlark.md). The source specification is Bazel's [Starlark Language
Specification][spec] at `c0af0ea03dc90d3bbc021394b693e6957cc15030`. The SHA-256
of raw `spec.md` is
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
The parse oracle uses [starlark-go][go] at
`4f4267fb140d1e8b91c9bce55cee2f809e8840dd`.

## Lean entry points

- `Frontend.lexUtf8` and `Frontend.lex` produce spanned tokens for logical
  lines. The byte entry point rejects ill-formed UTF-8 and highlights the first
  byte of the bad sequence. Positions use zero-based byte offsets and one-based
  lines and Unicode scalar columns in the original input. A tab occupies one
  source column. [Lexer](../../Silmaril/Languages/Starlark/Frontend/Lexer/Defs.lean)
- `Frontend.parseModuleUtf8` and `Frontend.parseModule` retain top-level
  statement spans. `ParsedModule.toSourceStmt` sequences the existing scalar
  AST in source order, with `pass` for an empty module. `Starlark.runModule`
  resolves and denotes that AST in the closed scalar environment. The module
  example evaluates `out = -1` through arithmetic, a conditional, and an untaken
  error branch. [Lean checks](../../Silmaril/Languages/Starlark/Frontend/Checks.lean)
- `Frontend.parseFunctionUtf8` and `Frontend.parseFunction` accept a file
  containing one `def` with required positional name parameters and a
  multiline suite. They return its name, ordered parameters, function span,
  and located direct body statements. `ParsedFunction.toSourceStmt` lowers
  branches and returns to the existing scalar body AST. Pass that AST and
  already bound globals and parameters to `Starlark.runFunctionBody`.
  [Parser](../../Silmaril/Languages/Starlark/Frontend/Defs.lean)

```starlark
def pick(flag):
  if flag:
    if (1 +
        2) == 3:
      return 8
    else:
      return 0
  else:
    return -1
```

The nested-suite fixture evaluates this body with `flag` bound to `True` and
`False`, yielding `8` and `-1`. It also exercises CRLF, Unicode comments, and
explicit line joining. A smaller multiline function with two open levels at
EOF has a kernel-checked text-to-denotation example. The existing soundness
proofs still begin at the resolved scalar AST, and static and dynamic failures
retain their existing types. Parser soundness and completeness remain open.
[Lean checks](../../Silmaril/Languages/Starlark/Frontend/Checks.lean)

## Module initialization

`Frontend.Module.parseUtf8` and `Frontend.Module.parse` lower complete files
to located `Modules.Resolve.Command`s. The module profile accepts top-level
scalar assignments and expression statements, multiline `def` declarations
with positional parameters and optional scalar defaults, call assignments
of the form `name = function(arg, ...)`, and leading load statements. The call is the entire right-hand side, and both
names are bare identifiers. The adapter reuses the logical-line, parameter,
and suite parsers. It emits a normalized declaration for each `def` and a
normalized `.call` expression for each call assignment. A top-level `pass`
produces no command. [Module adapter](../../Silmaril/Languages/Starlark/Frontend/Module/Defs.lean)

```starlark
# 雪
def id(x):
  return x
out = id(7)
```

`Frontend.Module.runUtf8` uses the existing `Modules.Resolve.runModule` with
an empty catalog, initial state, and linked table. The example publishes an
integer `out` with value `7`. Calling `id()` reaches a missing-argument error.
Using `id(missing)` rejects the undefined name during validation. The
result distinguishes a spanned frontend diagnostic, a normalized validation
error, and a runtime result with the existing residual state and publication
rules. Parsed commands retain half-open source spans. Backend errors retain
their native payloads because the normalized evaluator has no token-level
provenance. [Module checks](../../Silmaril/Languages/Starlark/Frontend/Module/Checks.lean)

The module body uses the same admitted scalar statement forms as the standalone
function parser. Its expressions, defaults, and call operands use integer
literals, names, `and`, `or`, and conditional expressions. Unary and binary
operators produce an unsupported diagnostic spanning the containing statement,
default, or argument. The profile excludes calls in function bodies and other
expression positions, plus keyword-only and variadic parameters.

### Defaults and call operands

```starlark
# 雪
seed = 7
def pick(seed=seed):
  return seed
out = pick()
override = pick(seed=9)
```

The default reads the defining module's `seed` when `pick` is installed. The
module publishes `out = 7` and `override = 9`. A separate control puts the
assignment to `seed` after `def` and supplies an explicit named override. It
still fails on the uninitialized default read at definition time.

Call arguments use the order positional, named, optional `*`, then optional
`**`. A call can contain at most one of each spread. `*` accepts a list or
tuple display of scalar operands. `**` accepts a dictionary display with
simple unescaped single- or double-quoted string keys and scalar values.
Collection displays in other positions and general spread expressions remain
outside the profile. The parser retains parameter, operand, and name/key
spans. It reports a spanned diagnostic for order errors because a grouped
normalized call cannot represent a misplaced operand.

The frontend preserves repeated explicit names so normalized validation can
reject them. It also passes required-after-default signatures to normalized
validation. Duplicate keys within a dictionary fail during display evaluation,
while a collision between an explicit named argument and a `**` key reaches
the binder and fails there. The Go controls exercise all three stages and
check the corresponding error messages.
[Module checks](../../Silmaril/Languages/Starlark/Frontend/Module/Checks.lean)

`Frontend.Module.initializes_iff_run` applies the existing module agreement
theorem to the normalized commands. `lowerNamedArguments_names` proves that
successful named-operand lowering preserves explicit names in order, including
repetitions. The kernel checks individual UTF-8 modules through publication
and reached errors, including omission of a definition-time default and a
positional/named binding collision. A general parser or source-to-normalized
adequacy theorem remains open. [Theorems](../../Silmaril/Languages/Starlark/Frontend/Module/Thms.lean)

### Leading loads and UTF-8 graphs

The module frontend accepts `load("label", "export")` and renamed imports
such as `load("label", local_name="export")`. A load requires at least one
import, preserves operand order, and permits a trailing comma. Labels and
export spellings use simple unescaped single- or double-quoted strings.
Export and alias names use the frontend's ASCII identifier profile. Parsed
syntax retains half-open spans for each load, its label, and the exported and
local names. The normalized command retains the whole load span. The existing
validator rejects private exports and conflicting bindings.

`Frontend.Module.Loader.prepare` accepts an array of UTF-8 texts and a caller-
supplied label-to-module-ID table for each text. Array positions are module
IDs. The adapter parses and resolves every supplied text in array order,
appending declarations to one table and retaining the spanned commands.
Frontend and validation errors identify the entry. Label lookup, export
lookup, any reached runtime error, and initialization of dependencies are
handled by the finite loader when a prepared module is requested. The adapter
treats label spellings as opaque strings. Filesystem access and path resolution
belong to the caller. The single-module `Frontend.Module.runUtf8` uses an empty
catalog. Use `Frontend.Module.Loader.loadUtf8` to prepare a graph and start a
cold load, or `Prepared.load` to reuse the matching loader session.
[UTF-8 loader](../../Silmaril/Languages/Starlark/Frontend/Module/Loader/Defs.lean)

For module 0, the producer text is

```starlark
# 雪
def id(x):
  return x
```

For module 1, the consumer supplies the label table `[("pkg:dep", 0)]` and
uses this text

```starlark
load("pkg:dep", imported="id")
out = imported(7)
```

The kernel-checked cold load publishes only `out = 7` from the consumer. A
missing export in the leading load leaves only the successful producer in the
cache and the consumer's first body assignment unexecuted. The Go controls
exercise both cases. They also run a late load with a missing export and
observe the preceding assignment. The frontend rejects late loads as outside
this leading-load profile. Nested loads, empty import lists, and private export
names have separate diagnostics or validation errors.
[Loader checks](../../Silmaril/Languages/Starlark/Frontend/Module/Loader/Checks.lean)

`Frontend.Module.Loader.runs_iff_load` reuses the existing agreement theorem
after preparation, on the normalized manifest and shared declaration table.
The two-module examples exercise specific source texts. General text adequacy
and a correspondence between Go's partial globals and the Lean session remain
open. [Loader theorem](../../Silmaril/Languages/Starlark/Frontend/Module/Loader/Thms.lean)

## Logical lines and layout

- LF, CRLF, and bare CR each end one physical line. Blank and comment-only
  lines contribute no newline or layout tokens. A physical break inside a
  matched `()`, `[]`, or `{}` pair is ignored for layout. A backslash
  immediately before a physical break also joins lines. Leading whitespace on
  the continuation line is ordinary whitespace.
- A significant line with more leading spaces opens an `indent` level. A
  smaller width must match an open level or zero, and emits one `outdent` per
  level closed. `indent` spans the leading spaces. Each `outdent` is zero-width
  at the first token of the new line. A mismatched dedent highlights its
  leading whitespace. Tabs are allowed between tokens and on ignored or
  continued lines. A tab in significant indentation is a `tabIndent` error
  under the pinned [space-only rule][layout-spec].
- EOF closes any remaining levels. When a final indented statement has no
  physical newline, the lexer inserts a zero-width newline before the
  zero-width outdents and EOF. The tests check that every successful token
  stream in the fixture corpus keeps a nonnegative layout depth and ends at
  depth zero with EOF as its final token.
- A stray or mismatched closing delimiter highlights the closer. An unclosed
  delimiter highlights the innermost unmatched opener. A missing suite and an
  unexpected indent are separate parser diagnostics. Function and statement
  spans end at their final code token. Nested source positions remain available
  in the token stream.

## Admitted surface

| Layer | Covered |
| --- | --- |
| Module statements | Name assignment, including a parenthesized name target, `pass`, and scalar expression statements. Newlines and semicolons separate simple statements. A final semicolon is allowed. |
| Function statements | The same simple statements, bare and valued `return`, and nested multiline `if`, `elif`, and `else` suites. Missing `else` lowers to `pass`. The module entry rejects top-level `if` and `return`. |
| Operands | ASCII names, parenthesized scalar expressions, and arbitrary-precision decimal, `0o`/`0O` octal, and `0x`/`0X` hexadecimal integers. Lexical resolution handles the names `None`, `True`, and `False`. |
| Precedence | Strongest first are unary `+`/`-`, `*`/`//`/`%`, `+`/`-`, comparisons, unary `not`, `and`, `or`, and `a if test else b`. Arithmetic and logical binaries associate left, comparisons are non-associative, and conditionals associate right in the `else` branch. |

`unsupported feature` identifies a boundary such as an inline suite, parameter
with a default, nested definition, or a call suffix. Later syntax in that
construct can still be malformed. Parameter binding, function installation, and
module publication remain outside the standalone function entry point. The
existing [Lean quotation](starlark-functions.md#quoting-an-expression-in-lean)
targets the normalized function language and uses Lean syntax.

The lexer retains the contents of simple unescaped quoted strings for load
operands and mapping spread keys. It identifies the closing delimiter and defers content and escape
validation for other quoted literals. Non-ASCII characters outside
comments and quoted literals are possible name characters pending Unicode
category checks. `exhausted` is an internal recursion guard bounded from input
length and token count.

## Pinned parser comparison

```sh
lake build --wfail +Silmaril.Languages.Starlark.Frontend.Checks \
  +Silmaril.Languages.Starlark.Frontend.Module.Checks \
  +Silmaril.Languages.Starlark.Frontend.Module.Loader.Checks +Silmaril.Languages.Starlark.Checks
scripts/starlark/frontend/run.sh
```

Use the repository Lean toolchain, Git, and Go 1.25 or newer. The oracle feeds
Go the same fixture strings as Lean and checks syntax acceptance with
zero-value `syntax.FileOptions`. The fixtures cover delimiter continuations,
explicit joining with LF, CRLF, and CR, ignored blank and comment lines,
multiple EOF outdents, and mismatched dedents. Both parsers accept inline tabs
and reject form feed and a backslash followed by a space. The module controls
also compile the same Go syntax trees and run successful programs with an
empty host. They compare integer `out` exports, default evaluation,
validation errors, and runtime errors with `out` still unbound. The
observations cover selected bindings and error phases. The Lean residual heap
and Go partial globals remain outside the comparison.

The pinned Go scanner accepts significant tabs. The fixtures observe one tab
or a space plus a tab aligned with eight spaces, and two tabs aligned with
fifteen spaces. Dedenting from sixteen spaces to two tabs fails in Go. The
Lean frontend rejects significant tabs under the core rule. Go also admits
`0b` integers and the name `assert`. Its syntax pass accepts an unassignable
scalar target, duplicate parameter names, top-level `if`, and top-level
`return`, with validation handled separately from syntax. The Lean frontend
reports those errors at its source boundary.
[Go scanner][go-scan] · [Oracle driver](../../scripts/starlark/frontend/run.sh)

## Next parser boundary

- Add inline suites and use the layout tokens for `for` and nested definitions.
  Extend the normalized module adapter with keyword-only and variadic
  parameters and additional call positions. Broader load spellings and
  positions can extend the leading-load profile.
- Extend expressions with tuple and collection displays, calls, attributes,
  indexing and slices. Add membership, the remaining operator levels,
  comprehensions, and lambdas as their target AST forms become available.
- Finish literal validation and decoding for strings, bytes, escapes, and
  floats. Add Unicode letter and decimal-digit classification for identifiers
  and carry nested source locations through the eventual module adapter.

[spec]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#lexical-elements
[layout-spec]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#special-tokens
[go]: https://github.com/google/starlark-go/tree/4f4267fb140d1e8b91c9bce55cee2f809e8840dd
[go-scan]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/syntax/scan.go#L495-L658
