module

public import Silmaril.Languages.Starlark.Defs
public import Silmaril.Languages.Starlark.Frontend.Lexer.Defs

/-! # Scalar Starlark source text

See `docs/projects/starlark-frontend.md` for the admitted grammar and diagnostics.
Resolution and denotation operate on the lowered `SourceStmt`.
-/

public section

namespace Silmaril.Languages.Starlark.Frontend

structure LocatedStmt where
  span : Span
  stmt : SourceStmt

structure ParsedModule where
  statements : List LocatedStmt

/-- A standalone scalar function whose body can be passed to `runFunctionBody`. -/
structure ParsedFunction where
  name : String
  parameters : List String
  span : Span
  body : List LocatedStmt

structure LocatedArgument where
  span : Span
  expr : SourceExpr

/-- The source forms consumed by the normalized module adapter. -/
inductive FileCommand where
  | simple (stmt : SourceStmt)
  | define (fn : ParsedFunction)
  | assignCall (target callee : String) (positional : List LocatedArgument)

structure LocatedFileCommand where
  span : Span
  command : FileCommand

private def sequence (statements : List LocatedStmt) : SourceStmt :=
  match statements.reverse with
  | [] => .pass
  | last :: preceding => preceding.foldl (fun rest first => .seq first.stmt rest) last.stmt

/-- Erase statement locations and compose the existing scalar AST in source order. -/
def ParsedModule.toSourceStmt (parsed : ParsedModule) : SourceStmt := sequence parsed.statements

/-- Lower the body in its function context, with parameters bound by the caller. -/
def ParsedFunction.toSourceStmt (parsed : ParsedFunction) : SourceStmt := sequence parsed.body

private structure Stream where
  remaining : List Token
  lastEnd : Position := {}

private def Stream.peek (s : Stream) : Token :=
  s.remaining.headD ⟨.eof, ⟨s.lastEnd, s.lastEnd⟩⟩

private def Stream.pop (s : Stream) : Stream :=
  let stop := match s.peek.kind with
    | .newline | .indent | .outdent | .eof => s.lastEnd
    | _ => s.peek.span.stop
  ⟨s.remaining.drop 1, stop⟩

private def failAt {α : Type} (kind : DiagnosticKind) (s : Stream) : Except Diagnostic α :=
  .error ⟨kind, s.peek.span⟩

private def expect {α : Type} (description : String) (s : Stream) : Except Diagnostic α :=
  failAt (.expected description) s

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
    | _ => return (left, s)

end

private def parseSmallStmt (exprFuel : Nat) (inFunction : Bool) (s : Stream) :
    Except Diagnostic (SourceStmt × Stream) := do
  match s.peek.kind with
  | .indent => failAt .unexpectedIndent s
  | .keyword "load" => failAt (.unsupported .loadStatement) s
  | .keyword "break" | .keyword "continue" => failAt (.unsupported .functionControl) s
  | .keyword "return" =>
    unless inFunction do return ← failAt .topLevelReturn s
    let next := s.pop
    match next.peek.kind with
    | .newline | .eof | .symbol ";" => return (.ret none, next)
    | _ =>
      let (value, rest) ← parseExpr exprFuel 0 next
      if rest.peek.kind = .symbol "," then failAt (.unsupported .tuple) rest
      else return (.ret (some value), rest)
  | .keyword "pass" => return (.pass, s.pop)
  | _ =>
    let (left, rest) ← parseExpr exprFuel 0 s
    match rest.peek.kind with
    | .symbol "=" =>
      let .read name := left
        | .error ⟨.invalidAssignmentTarget, ⟨s.peek.span.start, rest.lastEnd⟩⟩
      let (right, rest) ← parseExpr exprFuel 0 rest.pop
      if rest.peek.kind = .symbol "," then failAt (.unsupported .tuple) rest
      else return (.assign name right, rest)
    | .symbol "+=" | .symbol "-=" | .symbol "*=" | .symbol "/=" | .symbol "//=" | .symbol "%="
    | .symbol "&=" | .symbol "|=" | .symbol "^=" | .symbol "<<=" | .symbol ">>=" =>
      failAt (.unsupported .augmentedAssignment) rest
    | .symbol "," => failAt (.unsupported .tuple) rest
    | _ => return (.eval left, rest)

private def consumeSymbol (symbol : String) (s : Stream) : Except Diagnostic Stream :=
  if s.peek.kind = .symbol symbol then .ok s.pop else expect s!"'{symbol}'" s

private def finishSmallStmt (s : Stream) : Except Diagnostic (Bool × Stream) :=
  match s.peek.kind with
  | .eof => .ok (true, s)
  | .newline => .ok (true, s.pop)
  | .symbol ";" => .ok (false, s.pop)
  | _ => expect "a semicolon or end of line" s

-- The block loop consumes one statement or newline per iteration. Each descent
-- into a branch suite consumes the heading and its layout tokens.
mutual

private def parseBlock (exprFuel : Nat) (inFunction : Bool) :
    Nat → Bool → Stream → List LocatedStmt → Except Diagnostic (List LocatedStmt × Stream)
  | 0, _, s, _ => failAt .exhausted s
  | fuel + 1, lineStart, s, statements => do
    match s.peek.kind with
    | .eof | .outdent => return (statements.reverse, s)
    | .newline => parseBlock exprFuel inFunction fuel true s.pop statements
    | .keyword "def" | .keyword "for" =>
      if lineStart then failAt (.unsupported .compoundStatement) s
      else expect "a simple statement" s
    | .keyword "if" =>
      unless lineStart do return ← expect "a simple statement" s
      unless inFunction do return ← failAt .topLevelIf s
      let (stmt, rest) ← parseBranch exprFuel fuel s
      let located := ⟨⟨s.peek.span.start, rest.lastEnd⟩, stmt⟩
      parseBlock exprFuel inFunction fuel true rest (located :: statements)
    | _ =>
      let (stmt, rest) ← parseSmallStmt exprFuel inFunction s
      let statements := ⟨⟨s.peek.span.start, rest.lastEnd⟩, stmt⟩ :: statements
      let (lineStart, next) ← finishSmallStmt rest
      parseBlock exprFuel inFunction fuel lineStart next statements

private def parseSuite (exprFuel : Nat) :
    Nat → Stream → Except Diagnostic (List LocatedStmt × Stream)
  | 0, s => failAt .exhausted s
  | fuel + 1, s => do
    match s.peek.kind with
    | .eof => failAt .expectedIndentedSuite s
    | .newline =>
      let next := s.pop
      unless next.peek.kind = .indent do return ← failAt .expectedIndentedSuite next
      let (body, rest) ← parseBlock exprFuel true fuel true next.pop []
      if body.isEmpty then return ← failAt .expectedIndentedSuite rest
      unless rest.peek.kind = .outdent do return ← expect "an outdent" rest
      return (body, rest.pop)
    | _ => failAt (.unsupported .inlineSuite) s

private def parseBranch (exprFuel : Nat) : Nat → Stream → Except Diagnostic (SourceStmt × Stream)
  | 0, s => failAt .exhausted s
  | fuel + 1, s => do
    let (test, afterTest) ← parseExpr exprFuel 0 s.pop
    let (yes, rest) ← parseSuite exprFuel fuel (← consumeSymbol ":" afterTest)
    let (no, rest) ← match rest.peek.kind with
      | .keyword "elif" => parseBranch exprFuel fuel rest
      | .keyword "else" => do
        let (body, rest) ← parseSuite exprFuel fuel (← consumeSymbol ":" rest.pop)
        pure (sequence body, rest)
      | _ => pure (.pass, rest)
    return (.branch test (sequence yes) no, rest)

end

private def parserFuel (tokens : List Token) : Nat := 2 * tokens.length + 2

private def parseModuleTokens (tokens : List Token) : Except Diagnostic ParsedModule := do
  let fuel := parserFuel tokens
  let (statements, rest) ← parseBlock fuel false fuel true ⟨tokens, {}⟩ []
  unless rest.peek.kind = .eof do return ← expect "end of file" rest
  return ⟨statements⟩

/-- Parse decoded scalar module text, retaining top-level statement spans. -/
def parseModule (source : String) : Except Diagnostic ParsedModule := do
  parseModuleTokens (← lex source)

/-- Parse original UTF-8 file bytes with the same spans and grammar. -/
def parseModuleUtf8 (source : ByteArray) : Except Diagnostic ParsedModule := do
  parseModuleTokens (← lexUtf8 source)

private def parseName (s : Stream) : Except Diagnostic (String × Stream) :=
  match s.peek.kind with
  | .name name => .ok (name, s.pop)
  | .outside .nonAsciiName => failAt (.unsupported .nonAsciiName) s
  | _ => expect "a name" s

private def parseParameters : Nat → Stream → List String → Except Diagnostic (List String × Stream)
  | 0, s, _ => failAt .exhausted s
  | fuel + 1, s, names => do
    match s.peek.kind with
    | .symbol ")" => return (names.reverse, s.pop)
    | .symbol "*" | .symbol "**" => failAt (.unsupported .parameters) s
    | _ =>
      let (name, rest) ← parseName s
      if names.contains name then return ← failAt (.duplicateParameter name) s
      let names := name :: names
      match rest.peek.kind with
      | .symbol "," => parseParameters fuel rest.pop names
      | .symbol ")" => return (names.reverse, rest.pop)
      | .symbol "=" => failAt (.unsupported .parameters) rest
      | _ => expect "',' or ')'" rest

private def parseFunctionAt (fuel : Nat) (s : Stream) :
    Except Diagnostic (ParsedFunction × Stream) := do
  unless s.peek.kind = .keyword "def" do return ← expect "'def'" s
  let (name, rest) ← parseName s.pop
  let (parameters, rest) ← parseParameters fuel (← consumeSymbol "(" rest) []
  let (body, rest) ← parseSuite fuel fuel (← consumeSymbol ":" rest)
  return (⟨name, parameters, ⟨s.peek.span.start, rest.lastEnd⟩, body⟩, rest)

private def parseFunctionTokens (tokens : List Token) : Except Diagnostic ParsedFunction := do
  let (fn, rest) ← parseFunctionAt (parserFuel tokens) ⟨tokens, {}⟩
  unless rest.peek.kind = .eof do return ← failAt (.unsupported .functionFile) rest
  return fn

/-- Parse a file containing one scalar function with an indented body. -/
def parseFunction (source : String) : Except Diagnostic ParsedFunction := do
  parseFunctionTokens (← lex source)

/-- Parse a standalone function from original UTF-8 file bytes. -/
def parseFunctionUtf8 (source : ByteArray) : Except Diagnostic ParsedFunction := do
  parseFunctionTokens (← lexUtf8 source)

private def parsePositional (exprFuel : Nat) :
    Nat → Stream → List LocatedArgument → Except Diagnostic (List LocatedArgument × Stream)
  | 0, s, _ => failAt .exhausted s
  | fuel + 1, s, arguments => do
    match s.peek.kind with
    | .symbol ")" => return (arguments.reverse, s.pop)
    | .symbol "*" | .symbol "**" => failAt (.unsupported .callArguments) s
    | _ =>
      let (expr, rest) ← parseExpr exprFuel 0 s
      let arguments := ⟨⟨s.peek.span.start, rest.lastEnd⟩, expr⟩ :: arguments
      match rest.peek.kind with
      | .symbol "," => parsePositional exprFuel fuel rest.pop arguments
      | .symbol ")" => return (arguments.reverse, rest.pop)
      | .symbol "=" =>
        match s.peek.kind, s.pop.peek.kind with
        | .name _, .symbol "=" => failAt (.unsupported .callArguments) rest
        | _, _ => expect "',' or ')'" rest
      | _ => expect "',' or ')'" rest

private def hasExprSuffix (s : Stream) : Bool :=
  (infixOperator s).isSome || match s.peek.kind with
    | .keyword "if" | .symbol "(" | .symbol "[" | .symbol "." | .symbol ","
    | .symbol "/" | .symbol "|" | .symbol "^" | .symbol "&" | .symbol "<<" | .symbol ">>" => true
    | _ => false

private def parseFileSmall (exprFuel : Nat) (s : Stream) : Except Diagnostic (FileCommand × Stream) :=
  match s.remaining with
  | ⟨.name target, _⟩ :: ⟨.symbol "=", _⟩ :: ⟨.name callee, _⟩ :: ⟨.symbol "(", _⟩ :: _ => do
    let (arguments, rest) ← parsePositional exprFuel exprFuel s.pop.pop.pop.pop []
    if hasExprSuffix rest then failAt (.unsupported .call) rest
    else return (.assignCall target callee arguments, rest)
  | _ => (parseSmallStmt exprFuel false s).map fun (stmt, rest) => (.simple stmt, rest)

private def parseFileCommands (exprFuel : Nat) :
    Nat → Bool → Stream → List LocatedFileCommand → Except Diagnostic (List LocatedFileCommand)
  | 0, _, s, _ => failAt .exhausted s
  | fuel + 1, lineStart, s, commands => do
    match s.peek.kind with
    | .eof => return commands.reverse
    | .newline => parseFileCommands exprFuel fuel true s.pop commands
    | .keyword "def" =>
      unless lineStart do return ← expect "a simple statement" s
      let (fn, rest) ← parseFunctionAt exprFuel s
      parseFileCommands exprFuel fuel true rest (⟨fn.span, .define fn⟩ :: commands)
    | .keyword "if" | .keyword "for" =>
      unless lineStart do return ← expect "a simple statement" s
      if s.peek.kind = .keyword "if" then failAt .topLevelIf s
      else failAt (.unsupported .compoundStatement) s
    | _ =>
      let (command, rest) ← parseFileSmall exprFuel s
      let located := ⟨⟨s.peek.span.start, rest.lastEnd⟩, command⟩
      let (lineStart, next) ← finishSmallStmt rest
      parseFileCommands exprFuel fuel lineStart next (located :: commands)

private def parseFileTokens (tokens : List Token) : Except Diagnostic (List LocatedFileCommand) :=
  let fuel := parserFuel tokens
  parseFileCommands fuel fuel true ⟨tokens, {}⟩ []

/-- Parse a scalar file with definitions and direct call assignments. -/
def parseFile (source : String) : Except Diagnostic (List LocatedFileCommand) := do
  parseFileTokens (← lex source)

/-- Parse a scalar file with definitions and direct call assignments from UTF-8 bytes. -/
def parseFileUtf8 (source : ByteArray) : Except Diagnostic (List LocatedFileCommand) := do
  parseFileTokens (← lexUtf8 source)

end Silmaril.Languages.Starlark.Frontend
