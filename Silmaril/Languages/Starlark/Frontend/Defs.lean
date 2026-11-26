module

public import Silmaril.Languages.Starlark.Defs
public import Silmaril.Languages.Starlark.Frontend.Lexer.Defs

/-! # Scalar Starlark module text

See `docs/projects/starlark-frontend.md` for the admitted grammar and diagnostics.
Exercising resolution or denotation is a separate step on `toSourceStmt`.
-/

public section

namespace Silmaril.Languages.Starlark.Frontend

structure LocatedStmt where
  span : Span
  stmt : SourceStmt

structure ParsedModule where
  statements : List LocatedStmt

/-- Erase statement locations and compose the existing scalar AST in source order. -/
def ParsedModule.toSourceStmt (parsed : ParsedModule) : SourceStmt :=
  match parsed.statements.reverse with
  | [] => .pass
  | last :: preceding => preceding.foldl (fun rest first => .seq first.stmt rest) last.stmt

private structure Stream where
  remaining : List Token
  lastEnd : Position := {}

private def Stream.peek (s : Stream) : Token :=
  s.remaining.headD ⟨.eof, ⟨s.lastEnd, s.lastEnd⟩⟩

private def Stream.pop (s : Stream) : Stream := ⟨s.remaining.drop 1, s.peek.span.stop⟩

private def failAt {α : Type} (kind : DiagnosticKind) (s : Stream) : Except Diagnostic α :=
  .error ⟨kind, s.peek.span⟩

private def expect {α : Type} (description : String) (s : Stream) : Except Diagnostic α :=
  match s.peek.kind with
  | .outside .lineContinuation => failAt (.unsupported .lineContinuation) s
  | _ => failAt (.expected description) s

private inductive Infix where
  | arithmetic (priority : Nat) (op : BinaryOp)
  | comparison (op : Option BinaryOp)
  | logical (op : LogicalOp)

private def Infix.priority : Infix → Nat
  | .logical .or => 1
  | .logical .and => 2
  | .comparison _ => 4
  | .arithmetic p _ => p

private def infixOperator (s : Stream) : Option Infix :=
  match s.peek.kind with
  | .keyword "or" => some (.logical .or)
  | .keyword "and" => some (.logical .and)
  | .keyword "in" => some (.comparison none)
  | .keyword "not" =>
    if s.pop.peek.kind = .keyword "in" then some (.comparison none) else none
  | .symbol "==" => some (.comparison (some .eq))
  | .symbol "!=" => some (.comparison (some .ne))
  | .symbol "<" => some (.comparison (some .lt))
  | .symbol "<=" => some (.comparison (some .le))
  | .symbol ">" => some (.comparison (some .gt))
  | .symbol ">=" => some (.comparison (some .ge))
  | .symbol "+" => some (.arithmetic 5 .add)
  | .symbol "-" => some (.arithmetic 5 .sub)
  | .symbol "*" => some (.arithmetic 6 .mul)
  | .symbol "//" => some (.arithmetic 6 .floorDiv)
  | .symbol "%" => some (.arithmetic 6 .mod)
  | _ => none

-- Binding powers, from weakest to strongest, are conditional, or, and, not,
-- comparison, additive, multiplicative and unary sign. Primaries bind tighter.
-- Every recursive cycle consumes a token. The extra step covers the handoff
-- from an expression's prefix to its infix loop.
mutual

private def parseExpr : Nat → Nat → Stream → Except Diagnostic (SourceExpr × Stream)
  | 0, _, s => failAt .exhausted s
  | fuel + 1, minimum, s => do
    let next := s.pop
    let (left, rest) ← match s.peek.kind with
      | .name name => pure (.read name, next)
      | .integer value => pure (.int (Int.ofNat value), next)
      | .symbol "(" => do
        if next.peek.kind = .symbol ")" then failAt (.unsupported .tuple) s
        else
          let (expr, close) ← parseExpr fuel 0 next
          match close.peek.kind with
          | .symbol ")" => pure (expr, close.pop)
          | .symbol "," => failAt (.unsupported .tuple) close
          | _ => expect "')'" close
      | .symbol "+" => do
        let (arg, rest) ← parseExpr fuel 7 next
        pure (.unary .positive arg, rest)
      | .symbol "-" => do
        let (arg, rest) ← parseExpr fuel 7 next
        pure (.unary .negative arg, rest)
      | .keyword "not" => do
        unless minimum ≤ 3 do return ← expect "an expression" s
        let (arg, rest) ← parseExpr fuel 3 next
        pure (.unary .not arg, rest)
      | .keyword "lambda" =>
        if minimum == 0 then failAt (.unsupported .lambda) s else expect "an expression" s
      | .symbol "[" | .symbol "{" => failAt (.unsupported .collection) s
      | .symbol "~" => failAt (.unsupported .operator) s
      | .outside feature => failAt (.unsupported feature) s
      | _ => expect "an expression" s
    parseInfix fuel minimum false left rest

private def parseInfix : Nat → Nat → Bool → SourceExpr → Stream →
    Except Diagnostic (SourceExpr × Stream)
  | 0, _, _, _, s => failAt .exhausted s
  | fuel + 1, minimum, compared, left, s => do
    if let some op := infixOperator s then
      if op.priority < minimum then return (left, s)
      let next := s.pop
      match op with
      | .comparison op =>
        if compared then failAt .chainedComparison s
        else if let some op := op then
          let (right, rest) ← parseExpr fuel 5 next
          parseInfix fuel minimum true (.binary op left right) rest
        else failAt (.unsupported .operator) s
      | .arithmetic p op =>
        let (right, rest) ← parseExpr fuel (p + 1) next
        parseInfix fuel minimum compared (.binary op left right) rest
      | .logical op =>
        let p := (Infix.logical op).priority
        let (right, rest) ← parseExpr fuel (p + 1) next
        parseInfix fuel minimum false (.logical op left right) rest
    else match s.peek.kind with
    | .keyword "if" =>
      if minimum != 0 then return (left, s)
      let (test, afterTest) ← parseExpr fuel 1 s.pop
      unless afterTest.peek.kind = .keyword "else" do return ← expect "'else'" afterTest
      let (no, rest) ← parseExpr fuel 0 afterTest.pop
      return (.conditional test left no, rest)
    | .keyword "not" => expect "'in' after 'not'" s.pop
    | .symbol "(" => failAt (.unsupported .call) s
    | .symbol "[" => failAt (.unsupported .subscript) s
    | .symbol "." => failAt (.unsupported .attribute) s
    | .symbol "/" | .symbol "|" | .symbol "^" | .symbol "&" | .symbol "<<" | .symbol ">>" =>
      failAt (.unsupported .operator) s
    | .outside .lineContinuation => failAt (.unsupported .lineContinuation) s
    | _ => return (left, s)

end

private def parseStmt (fuel : Nat) (s : Stream) : Except Diagnostic (SourceStmt × Stream) := do
  match s.peek.kind with
  | .indent => failAt .unexpectedIndent s
  | .keyword "def" | .keyword "for" | .keyword "if" => failAt (.unsupported .compoundStatement) s
  | .keyword "load" => failAt (.unsupported .loadStatement) s
  | .keyword "return" | .keyword "break" | .keyword "continue" => failAt (.unsupported .functionControl) s
  | .keyword "pass" => return (.pass, s.pop)
  | _ =>
    let (left, rest) ← parseExpr fuel 0 s
    match rest.peek.kind with
    | .symbol "=" =>
      let .read name := left
        | .error ⟨.invalidAssignmentTarget, ⟨s.peek.span.start, rest.lastEnd⟩⟩
      let (right, rest) ← parseExpr fuel 0 rest.pop
      if rest.peek.kind = .symbol "," then failAt (.unsupported .tuple) rest
      else return (.assign name right, rest)
    | .symbol "+=" | .symbol "-=" | .symbol "*=" | .symbol "/=" | .symbol "//=" | .symbol "%="
    | .symbol "&=" | .symbol "|=" | .symbol "^=" | .symbol "<<=" | .symbol ">>=" =>
      failAt (.unsupported .augmentedAssignment) rest
    | .symbol "," => failAt (.unsupported .tuple) rest
    | _ => return (.eval left, rest)

private def parseStmts (exprFuel : Nat) : Nat → Stream → List LocatedStmt →
    Except Diagnostic ParsedModule
  | 0, s, _ => failAt .exhausted s
  | fuel + 1, s, statements => do
    match s.peek.kind with
    | .eof => return ⟨statements.reverse⟩
    | .newline => parseStmts exprFuel fuel s.pop statements
    | _ =>
      let (stmt, rest) ← parseStmt exprFuel s
      let statements := ⟨⟨s.peek.span.start, rest.lastEnd⟩, stmt⟩ :: statements
      match rest.peek.kind with
      | .eof => return ⟨statements.reverse⟩
      | .newline | .symbol ";" => parseStmts exprFuel fuel rest.pop statements
      | _ => expect "a semicolon or end of line" rest

private def parseTokens (tokens : List Token) : Except Diagnostic ParsedModule :=
  let count := tokens.length
  parseStmts (2 * count + 2) (count + 1) ⟨tokens, {}⟩ []

/-- Parse decoded scalar module text, retaining top-level statement spans. -/
def parseModule (source : String) : Except Diagnostic ParsedModule := do
  parseTokens (← lex source)

/-- Parse original UTF-8 file bytes with the same spans and grammar. -/
def parseModuleUtf8 (source : ByteArray) : Except Diagnostic ParsedModule := do
  parseTokens (← lexUtf8 source)

end Silmaril.Languages.Starlark.Frontend
