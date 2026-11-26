# Starlark source frontend

This frontend reads module text in a scalar subset of the [pinned Starlark core
profile](starlark.md). The source specification is Bazel's [Starlark Language
Specification][spec] at `c0af0ea03dc90d3bbc021394b693e6957cc15030`. The SHA-256
of raw `spec.md` is
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
The parse oracle uses [starlark-go][go] at
`4f4267fb140d1e8b91c9bce55cee2f809e8840dd`.

## Lean entry points

- `Frontend.lexUtf8` and `Frontend.lex` produce tokens with half-open spans,
  including a zero-width EOF token. The byte entry point rejects ill-formed
  UTF-8 and highlights the first byte of the bad sequence. Positions refer to
  the original bytes and use zero-based byte offsets and one-based lines and
  Unicode scalar columns. A tab occupies one column. LF, CRLF, and CR each end
  one line. [Lexer](../../Silmaril/Languages/Starlark/Frontend/Lexer/Defs.lean)
- `Frontend.parseModuleUtf8` and `Frontend.parseModule` produce a `ParsedModule`
  or a structured `Diagnostic`. The result retains a span for each top-level
  statement. `ParsedModule.toSourceStmt` erases locations and sequences the
  existing scalar AST in source order, with `pass` for an empty module.
  [Parser](../../Silmaril/Languages/Starlark/Frontend/Defs.lean)
- `Starlark.runModule` resolves and denotes that AST using the existing
  closed scalar environment. Its static and dynamic errors keep their existing
  types. The fixture below checks the output `out = -1` in Lean. It also
  exercises UTF-8 comments, statement order, exact integers, floor division,
  precedence, short-circuiting and the untaken error branch.
  [Lean checks](../../Silmaril/Languages/Starlark/Frontend/Checks.lean)

```starlark
# coût 😀
base = 0x10 + 0o3 * 2
out = -base // 5 + 4 if not False and 2 < 3 else 1 // 0
```

The implementation imports the scalar AST. The checks also import the scalar
resolver and denotation. The separate [Lean expression
quotation](starlark-functions.md#quoting-an-expression-in-lean) runs on Lean
syntax and targets the function language's normalized AST.
The existing soundness theorems still begin at the resolved scalar AST.
Parser soundness and completeness remain open.

## Admitted surface

| Layer | Covered |
| --- | --- |
| Text | UTF-8 input, Unicode comments, blank lines, inline spaces and tabs, an optional final newline, implicit line joining inside parentheses. Leading whitespace on a nonblank module line is an error. |
| Statements | Name assignment, including a parenthesized name target, `pass`, and scalar expression statements. Newlines and semicolons separate statements. A final semicolon is allowed. |
| Operands | ASCII identifiers, parenthesized scalar expressions, and arbitrary-precision decimal, `0o`/`0O` octal, and `0x`/`0X` hexadecimal integers. `None`, `True`, and `False` are names handled by lexical resolution. |
| Precedence | Strongest first: unary `+`/`-`, `*`/`//`/`%`, `+`/`-`, `==`/`!=`/`<`/`<=`/`>`/`>=`, unary `not`, `and`, `or`, then `a if test else b`. Binary arithmetic and logical operators associate left, comparisons are non-associative, and conditional expressions associate right in their `else` branch. |

The lexer validates bytes and token spellings before the parser runs. Syntax
errors in the admitted grammar include a missing operand or delimiter,
misplaced indentation, reserved words, malformed integers and chained
comparisons. `unsupported feature` marks a recognizable boundary, such as a
call suffix or a suite introducer. The remainder of the construct may contain
syntax errors. The lexer finds the closing delimiter for quoted literals and
defers validation of their contents and escapes. Non-ASCII characters outside comments and quoted
literals are treated as possible name characters without checking Unicode
categories. `exhausted` is a separate internal recursion guard, bounded from
the input length and token count.

Run the warning-fatal Lean checks and the pinned oracle from the repository
root with the repository toolchain, Git, and Go 1.25 or newer.

```sh
lake build --wfail +Silmaril.Languages.Starlark.Frontend.Checks +Silmaril.Languages.Starlark.Checks
scripts/starlark/frontend/run.sh
```

The oracle reads the same fixture strings as Lean and calls Go's parser with
zero-value `syntax.FileOptions`, before name resolution or execution. It checks
acceptance of the implemented subset and selected forms beyond it, plus
rejection of malformed inputs. Three fixtures deliberately record different
outcomes. Go accepts `0b` integer syntax and permits `assert` as a name, which
the pinned core specification excludes. Go's parser accepts `1 = 2` and leaves
assignability to its resolver. The Lean frontend rejects that target while
normalizing the statement. Lean byte-level fixtures additionally check a
malformed UTF-8 span, along with EOF, CRLF, and non-ASCII source positions.
[Oracle driver](../../scripts/starlark/frontend/run.sh)

## Next parser boundary

- Add logical line joining for explicit continuations and an indentation stack
  with indent and outdent tokens. Parse indented and inline suites and keep
  dedent and delimiter diagnostics tied to their source spans.
- Extend expressions with tuple and collection displays, calls, attributes,
  indexing and slices. Add membership, the remaining operator levels,
  comprehensions, and lambdas as their target AST forms become available.
- Add statement forms for load, function definitions and parameters, `if` and
  `for` suites, function and loop controls, destructuring and store targets.
  Connect these to the existing normalized module and function adapters.
- Finish literal validation and decoding for strings, bytes, escapes, and
  floats. Add Unicode letter and decimal-digit classification for identifiers.
  Extend locations to nested syntax and across resolution as the AST adapter
  acquires that information.

[spec]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#lexical-elements
[go]: https://github.com/google/starlark-go/tree/4f4267fb140d1e8b91c9bce55cee2f809e8840dd
