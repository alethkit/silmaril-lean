module

public import Silmaril.Languages.Starlark.Frontend.Defs
import all Silmaril.Languages.Starlark.Frontend.Defs
import all Silmaril.Languages.Starlark.Frontend.Lexer.Defs
import all Silmaril.Languages.Starlark.Denotation.Defs
import all Silmaril.Languages.Starlark.Resolve.Defs
meta import Silmaril.Languages.Starlark.Defs

namespace Silmaril.Languages.Starlark.Frontend

public structure Fixture where
  name : String
  source : String
  diagnostic : Option DiagnosticKind
  goAccepts : Bool

private def accept (name source : String) : Fixture := ⟨name, source, none, true⟩

private def reject (name source : String) (kind : DiagnosticKind) : Fixture :=
  ⟨name, source, some kind, false⟩

private def outside (name source : String) (feature : Feature) : Fixture :=
  ⟨name, source, some (.unsupported feature), true⟩

private def multiline := "# λ🙂\r\nout = (2 +\r\n  3)  # 文\r\nnext = out"

private def denotationSource :=
  "# coût 😀\nbase = 0x10 + 0o3 * 2\nout = -base // 5 + 4 if not False and 2 < 3 else 1 // 0"

/-- Both parsers receive the same source spelling. Go's result is syntax-only. -/
public def fixtures : List Fixture := [
  accept "empty" "",
  accept "comment-only" "  # 雪\n \t\n",
  accept "multiline-crlf" multiline,
  accept "bare-cr" "x = 1\ry = x",
  accept "denotation" denotationSource,
  accept "simple-statements" "pass; (x) = 0; x;\n",
  accept "associativity" "x = (+20 - 8 - 3) % 4 or 0 and None",
  accept "parenthesized-comparison" "x = (1 < 2) == True",
  accept "upper-radix-and-big-int" "out = 0XFF + 0O7 + 123456789012345678901234567890",
  accept "duplicate-global-syntax" "x = 1\nx = 2\n",
  reject "missing-rhs" "x = # nothing follows\n" (.expected "an expression"),
  reject "missing-group-closer" "x = (1 + 2" (.expected "')'"),
  reject "missing-else" "x = 1 if True" (.expected "'else'"),
  reject "chained-comparison" "x = 1 <= 2 < 3" .chainedComparison,
  reject "chained-membership" "x = 1 == 2 not in values" .chainedComparison,
  reject "not-incomplete" "x = 1 not 2" (.expected "'in' after 'not'"),
  reject "not-after-add" "x = 1 + not False" (.expected "an expression"),
  reject "missing-statement-separator" "x = 1 y = 2" (.expected "a semicolon or end of line"),
  reject "invalid-character" "x = !1" (.invalidCharacter '!'),
  reject "leading-zero" "x = 0755" .invalidInteger,
  reject "invalid-radix" "x = 0o8" .invalidInteger,
  reject "invalid-exponent" "x = 1e-" .invalidFloat,
  reject "unclosed-quote" "x = 'hello\n" .unterminatedQuote,
  reject "unexpected-indent" "  x = 1\n" .unexpectedIndent,
  outside "unicode-name" "λ = 1\nout = λ" .nonAsciiName,
  outside "suite" "def f():\n    return 1\n" .compoundStatement,
  outside "load" "load('a.star', 'name')" .loadStatement,
  outside "tuple-rhs" "x = 1, 2" .tuple,
  outside "collection" "x = [1]" .collection,
  outside "call" "x = f(2)" .call,
  outside "subscript" "x = a[2]" .subscript,
  outside "attribute" "x = a.field" .attribute,
  outside "shift" "x = 1 << 2" .operator,
  outside "membership" "x = 1 not in a" .operator,
  outside "float" "x = .25e+2" .floatLiteral,
  outside "quoted" "x = rb'''雪\n# still part of the literal'''" .quotedLiteral,
  outside "continuation" "x = 1 + \\\n  2" .lineContinuation,
  ⟨"unassignable-target", "1 = 2", some .invalidAssignmentTarget, true⟩,
  ⟨"go-binary-literal", "x = 0b10", some .invalidInteger, true⟩,
  ⟨"go-assert-name", "assert = 2", some (.reservedWord "assert"), true⟩]

private def Fixture.check (fixture : Fixture) : Bool :=
  match parseModuleUtf8 fixture.source.toUTF8 with
  | .ok _ => fixture.diagnostic.isNone
  | .error error => decide (fixture.diagnostic = some error.kind)

#guard fixtures.all Fixture.check

private def denotedGlobal (source name : String) : Option Value :=
  (do
    let parsed ← (parseModuleUtf8 source.toUTF8).toOption
    let globals ← (runModule parsed.toSourceStmt).toOption
    globals name)

-- UTF-8 file bytes → scalar AST → unchanged resolver and denotation.
#guard decide (denotedGlobal denotationSource "out" = some (.int (-1)))

example : denotedGlobal "out = 2 + 3" "out" = some (.int 5) := by decide +kernel

#guard decide (denotedGlobal "x = 20 - 8 - 3" "x" = some (.int 9) ∧
    denotedGlobal "y = 1 or 0 and 0" "y" = some (.int 1) ∧
    denotedGlobal "z = 1 if True else 2 if False else 3" "z" = some (.int 1) ∧
    denotedGlobal "z = not 2 < 3" "z" = some (.bool false))

private def endToEndFailure (source : String) : Option Failure :=
  match parseModule source with
  | .ok parsed =>
    match runModule parsed.toSourceStmt with
    | .error failure => some failure
    | .ok _ => none
  | .error _ => none

#guard decide (endToEndFailure "x = 1\nx = 2" = some (.static (.duplicateGlobal "x")) ∧
    endToEndFailure "x = 1 // 0" = some (.dynamic (.zeroDivisor .floorDiv)))

private def statementSpans : Option (List Span) := do
  let parsed ← (parseModuleUtf8 multiline.toUTF8).toOption
  return parsed.statements.map LocatedStmt.span

example : statementSpans = some [⟨⟨10, 2, 1⟩, ⟨26, 3, 5⟩⟩, ⟨⟨35, 4, 1⟩, ⟨45, 4, 11⟩⟩] :=
  by decide +kernel

private def newlineSpans : Option (List Span) := do
  let tokens ← (lex multiline).toOption
  return (tokens.filter (fun t => decide (t.kind = .newline))).map Token.span

example : newlineSpans = some [⟨⟨8, 1, 5⟩, ⟨10, 2, 1⟩⟩, ⟨⟨33, 3, 10⟩, ⟨35, 4, 1⟩⟩] :=
  by decide +kernel

private def diagnostic (source : ByteArray) : Option Diagnostic :=
  match parseModuleUtf8 source with
  | .ok _ => none
  | .error error => some error

example : diagnostic ("# 文\r\nx =".toUTF8) =
    some ⟨.expected "an expression", ⟨⟨10, 2, 4⟩, ⟨10, 2, 4⟩⟩⟩ := by decide +kernel

example : diagnostic ("x = café".toUTF8) =
    some ⟨.unsupported .nonAsciiName, ⟨⟨4, 1, 5⟩, ⟨9, 1, 9⟩⟩⟩ := by decide +kernel

example : diagnostic ("# λ\r\n# 😀".toUTF8.push 0xC0) =
    some ⟨.invalidUtf8, ⟨⟨12, 2, 4⟩, ⟨13, 2, 5⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend
