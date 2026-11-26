module

public import Init

/-! UTF-8 source positions, diagnostics and tokens for the scalar Starlark frontend. -/

public section

namespace Silmaril.Languages.Starlark.Frontend

/-- Zero-based byte offset and one-based line and Unicode scalar column. -/
structure Position where
  byte : Nat := 0
  line : Nat := 1
  column : Nat := 1
  deriving DecidableEq, Repr, Inhabited

/-- A half-open range in the original input. -/
structure Span where
  start : Position
  stop : Position
  deriving DecidableEq, Repr, Inhabited

inductive Feature where
  | nonAsciiName | lineContinuation
  | floatLiteral | quotedLiteral
  | compoundStatement | loadStatement | functionControl
  | augmentedAssignment
  | tuple | collection | lambda | call | subscript | attribute | operator
  deriving DecidableEq, Repr

inductive DiagnosticKind where
  | invalidUtf8
  | invalidCharacter (c : Char)
  | invalidInteger | invalidFloat | unterminatedQuote | unexpectedIndent
  | reservedWord (word : String)
  | expected (description : String)
  | chainedComparison | invalidAssignmentTarget
  | unsupported (feature : Feature)
  | exhausted
  deriving DecidableEq, Repr

structure Diagnostic where
  kind : DiagnosticKind
  span : Span
  deriving DecidableEq, Repr

inductive TokenKind where
  | name (text : String)
  | integer (value : Nat)
  | keyword (text : String)
  | symbol (text : String)
  | newline | indent | eof
  | outside (feature : Feature)
  deriving DecidableEq, Repr, Inhabited

structure Token where
  kind : TokenKind
  span : Span
  deriving DecidableEq, Repr, Inhabited

private def isNewline (c : Char) : Bool := c == '\n' || c == '\r'

private def Position.advance (p : Position) (c : Char) (width : Nat := c.utf8Size) : Position :=
  if isNewline c then ⟨p.byte + width, p.line + 1, 1⟩
  else ⟨p.byte + width, p.line, p.column + 1⟩

private structure Cursor where
  rest : List Char
  pos : Position := {}

private def Cursor.pop (s : Cursor) : Cursor :=
  match s.rest with
  | '\r' :: '\n' :: rest => ⟨rest, s.pos.advance '\r' 2⟩
  | c :: rest => ⟨rest, s.pos.advance c⟩
  | [] => s

private def Cursor.popN (s : Cursor) (n : Nat) : Cursor :=
  match n with
  | 0 => s
  | n + 1 => s.pop.popN n

-- Used only for runs that contain no line breaks.
private def takeRun (test : Char → Bool) (pos : Position) (text : String) :
    List Char → String × Cursor
  | c :: cs =>
    if test c then takeRun test (pos.advance c) (text.push c) cs
    else (text, ⟨c :: cs, pos⟩)
  | [] => (text, ⟨[], pos⟩)

private def Cursor.take (s : Cursor) (test : Char → Bool) : String × Cursor :=
  takeRun test s.pos "" s.rest

private def skipLine (pos : Position) : List Char → Cursor
  | c :: cs => if isNewline c then ⟨c :: cs, pos⟩ else skipLine (pos.advance c) cs
  | [] => ⟨[], pos⟩

private def containsPrefix (s : Cursor) (p : String) : Bool := p.toList.isPrefixOf s.rest

private def failAt {α : Type} (kind : DiagnosticKind) (start stop : Position) :
    Except Diagnostic α := .error ⟨kind, ⟨start, stop⟩⟩

private def nameStart (c : Char) : Bool := c.isAlpha || c == '_' || c.toNat ≥ 128

private def word (s : Cursor) : Except Diagnostic (TokenKind × Cursor) := do
  let (name, next) := s.take (fun c => nameStart c || c.isDigit)
  if ["as", "assert", "async", "await", "class", "del", "except", "finally", "from", "global",
      "import", "is", "nonlocal", "raise", "try", "while", "with", "yield"].contains name then
    failAt (.reservedWord name) s.pos next.pos
  else if ["and", "break", "continue", "def", "elif", "else", "for", "if", "in", "lambda",
      "load", "not", "or", "pass", "return"].contains name then
    return (.keyword name, next)
  else if name.toList.any (fun c => c.toNat ≥ 128) then
    return (.outside .nonAsciiName, next)
  else
    return (.name name, next)

private def digitValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 16

private def number (s : Cursor) : Except Diagnostic (TokenKind × Cursor) := do
  match s.rest with
  | '0' :: radix :: _ =>
    if ['x', 'X', 'o', 'O', 'b', 'B'].contains radix then
      let base := if radix == 'x' || radix == 'X' then 16 else 8
      let (digits, next) := (s.popN 2).take (fun c => nameStart c || c.isDigit)
      if radix == 'b' || radix == 'B' || digits.isEmpty ||
          digits.toList.any (fun c => digitValue c ≥ base) then
        return ← failAt .invalidInteger s.pos next.pos
      return (.integer (digits.toList.foldl (fun n c => n * base + digitValue c) 0), next)
  | _ => pure ()
  let (digits, afterDigits) := s.take Char.isDigit
  let fraction := afterDigits.rest.head? == some '.'
  let afterFraction :=
    if fraction then (afterDigits.pop.take Char.isDigit).2 else afterDigits
  let exp := afterFraction.rest.head?.any (fun c => c == 'e' || c == 'E')
  if exp then
    let afterE := afterFraction.pop
    let exponentStart :=
      if afterE.rest.head?.any (fun c => c == '+' || c == '-') then afterE.pop else afterE
    let (exponent, next) := exponentStart.take Char.isDigit
    if exponent.isEmpty then failAt .invalidFloat s.pos next.pos
    else return (.outside .floatLiteral, next)
  else if fraction then
    return (.outside .floatLiteral, afterFraction)
  else if digits.length > 1 && digits.startsWith "0" then
    failAt .invalidInteger s.pos afterDigits.pos
  else
    return (.integer (digits.toList.foldl (fun n c => n * 10 + digitValue c) 0), afterDigits)

private def quotePrefix (s : Cursor) : Nat :=
  let isQuote (c : Char) := c == '\'' || c == '"'
  match s.rest with
  | a :: b :: c :: _ =>
    if ((a == 'r' && b == 'b') || (a == 'b' && b == 'r')) && isQuote c then 2
    else if (a == 'r' || a == 'b') && isQuote b then 1 else 0
  | a :: b :: _ => if (a == 'r' || a == 'b') && isQuote b then 1 else 0
  | _ => 0

/-- Find the closing delimiter without interpreting contents or escape values. -/
private def closeQuote (start : Position) (delimiter : String) (triple : Bool) :
    Nat → Cursor → Except Diagnostic Cursor
  | 0, s => failAt .exhausted s.pos s.pos
  | fuel + 1, s =>
    if containsPrefix s delimiter then return s.popN delimiter.length
    else match s.rest with
    | [] => failAt .unterminatedQuote start s.pos
    | '\\' :: _ => closeQuote start delimiter triple fuel (s.popN 2)
    | c :: _ =>
      if !triple && isNewline c then failAt .unterminatedQuote start s.pos
      else closeQuote start delimiter triple fuel s.pop

private def quoted (fuel : Nat) (start : Cursor) (prefixLength : Nat) (c : Char) :
    Except Diagnostic (TokenKind × Cursor) := do
  let opener := start.popN prefixLength
  let long := String.ofList [c, c, c]
  let triple := containsPrefix opener long
  let delimiter := if triple then long else String.singleton c
  let next ← closeQuote start.pos delimiter triple fuel (opener.popN delimiter.length)
  return (.outside .quotedLiteral, next)

-- Longest punctuation first. A standalone '!' or '\' is not punctuation.
private def punctuation : List String :=
  ["//=", "<<=", ">>=", "//", "<<", ">>", "**", "==", "!=", "<=", ">=", "+=", "-=", "*=",
   "/=", "%=", "&=", "|=", "^=", "+", "-", "*", "/", "%", "~", "&", "|", "^", ".", ",", "=",
   ";", ":", "(", ")", "[", "]", "{", "}", "<", ">"]

private def scanToken (fuel : Nat) (s : Cursor) (c : Char) :
    Except Diagnostic (TokenKind × Cursor) := do
  let prefixLength := quotePrefix s
  if c == '\'' || c == '"' then quoted fuel s 0 c
  else if prefixLength != 0 then quoted fuel s prefixLength ((s.popN prefixLength).rest.headD c)
  else if nameStart c then word s
  else if c.isDigit || (c == '.' && s.rest[1]?.any Char.isDigit) then number s
  else if c == '\\' && s.rest[1]?.any isNewline then
    return (.outside .lineContinuation, s.pop.pop)
  else if let some symbol := punctuation.find? (containsPrefix s) then
    return (.symbol symbol, s.popN symbol.length)
  else failAt (.invalidCharacter c) s.pos s.pop.pos

private def scan : Nat → Cursor → Bool → Nat → List Token → Except Diagnostic (List Token)
  | 0, s, _, _, _ => failAt .exhausted s.pos s.pos
  | fuel + 1, s, lineStart, depth, tokens => do
    match s.rest with
    | [] => return (⟨.eof, ⟨s.pos, s.pos⟩⟩ :: tokens).reverse
    | c :: cs =>
      if isNewline c then
        let next := s.pop
        let tokens := if depth == 0 then ⟨.newline, ⟨s.pos, next.pos⟩⟩ :: tokens else tokens
        scan fuel next true depth tokens
      else if c == '#' then
        scan fuel (skipLine (s.pos.advance c) cs) false depth tokens
      else if c == ' ' || c == '\t' then
        let (_, next) := s.take (fun c => c == ' ' || c == '\t')
        let indented := lineStart && depth == 0 &&
          next.rest.head?.any (fun c => c != '#' && !isNewline c)
        let tokens := if indented then ⟨.indent, ⟨s.pos, next.pos⟩⟩ :: tokens else tokens
        scan fuel next false depth tokens
      else
        let (kind, next) ← scanToken (fuel + 1) s c
        let depth := match kind with
          | .symbol "(" | .symbol "[" | .symbol "{" => depth + 1
          | .symbol ")" | .symbol "]" | .symbol "}" => depth - 1
          | _ => depth
        scan fuel next false depth (⟨kind, ⟨s.pos, next.pos⟩⟩ :: tokens)

/-- Lex decoded text. Nonblank leading whitespace outside delimiters emits an
`indent` marker, and LF, CRLF and CR each count as one physical newline. -/
def lex (source : String) : Except Diagnostic (List Token) :=
  let chars := source.toList
  scan (chars.length + 1) ⟨chars, {}⟩ true 0 []

-- Locate the first bad sequence on the invalid-input path only.
private def badUtf8 (bytes : ByteArray) : Nat → Position → Diagnostic
  | 0, pos => ⟨.invalidUtf8, ⟨pos, pos⟩⟩
  | fuel + 1, pos =>
    match bytes.utf8DecodeChar? pos.byte with
    | none => ⟨.invalidUtf8, ⟨pos, { pos with byte := pos.byte + 1, column := pos.column + 1 }⟩⟩
    | some c =>
      let width := if c == '\r' && bytes[pos.byte + 1]? == some 10 then 2 else c.utf8Size
      badUtf8 bytes fuel (pos.advance c width)

/-- Lex original file bytes, rejecting malformed UTF-8 before scanning. -/
def lexUtf8 (bytes : ByteArray) : Except Diagnostic (List Token) :=
  match String.fromUTF8? bytes with
  | some text => lex text
  | none => .error (badUtf8 bytes bytes.size {})

end Silmaril.Languages.Starlark.Frontend
