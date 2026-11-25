module

public import Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
public meta import Lean.Elab.Term

public meta section

namespace Silmaril.Languages.Starlark.Functions.Lowering.Quote

open Lean

declare_syntax_cat starlarkExpr
declare_syntax_cat starlarkArg

syntax:max ident : starlarkExpr
syntax:max num : starlarkExpr
syntax:max str : starlarkExpr
syntax:max "(" starlarkExpr ")" : starlarkExpr
syntax:max starlarkExpr:max "(" starlarkArg,*,? ")" : starlarkExpr
syntax:75 "-" starlarkExpr:75 : starlarkExpr
scoped syntax:30 starlarkExpr:30 " and " starlarkExpr:31 : starlarkExpr
scoped syntax:25 starlarkExpr:25 " or " starlarkExpr:26 : starlarkExpr
syntax:10 starlarkExpr:11 " if " starlarkExpr:11 " else " starlarkExpr:10 : starlarkExpr

syntax "**" starlarkExpr : starlarkArg
syntax "*" starlarkExpr : starlarkArg
syntax ident " = " starlarkExpr : starlarkArg
syntax starlarkExpr : starlarkArg

-- Recognize common unadmitted forms to point to the relevant token.
syntax:60 starlarkExpr:60 " + " starlarkExpr:61 : starlarkExpr
syntax:max starlarkExpr:max "[" starlarkExpr "]" : starlarkExpr
syntax:max "[" starlarkExpr,*,? "]" : starlarkExpr

/-- Quote one expression as a normalized, unresolved `Resolve.SourceExpr` term. -/
scoped syntax "starlark%[" starlarkExpr "]" : term

private meta def quoteName (identifier : TSyntax `ident) : MacroM String := do
  let .ident _ raw (.str .anonymous name) _ := identifier.raw
    | Macro.throwErrorAt identifier "expected an unqualified Starlark identifier"
  let startsName (c : Char) := c.isAlpha || c == '_'
  let first := name.toList.head?
  unless raw.toString == name && first.any startsName &&
      name.toList.all (fun c => startsName c || c.isDigit) do
    Macro.throwErrorAt identifier "expected an unescaped ASCII Starlark identifier"
  let reserved := ["and", "else", "load", "break", "for", "not", "continue", "if", "or",
    "def", "in", "pass", "elif", "lambda", "return", "as", "global", "assert", "import",
    "async", "is", "await", "nonlocal", "class", "raise", "del", "try", "except", "while",
    "finally", "with", "from", "yield"]
  if reserved.contains name then
    Macro.throwErrorAt identifier s!"reserved Starlark keyword '{name}'"
  return name

private meta def checkDecimal (literal : TSyntax `num) : MacroM Unit := do
  unless literal.raw[0].getAtomVal == toString literal.getNat do
    Macro.throwErrorAt literal "expected a decimal integer without separators or leading zeros"

private meta def quoteCall (callee : TSyntax `starlarkExpr) (args : Array (TSyntax `starlarkArg)) :
    MacroM (TSyntax `term) := do
  let mut positional := #[]
  let mut keywords := #[]
  let mut names : Array String := #[]
  let mut star : Option (TSyntax `term) := none
  let mut starStar : Option (TSyntax `term) := none
  for arg in args do
    if starStar.isSome then
      Macro.throwErrorAt arg "no argument may follow '**'"
    match arg with
    | `(starlarkArg| **$value) =>
      starStar := some (← `(starlark%[$value]))
    | `(starlarkArg| *$value) =>
      if star.isSome then
        Macro.throwErrorAt arg "only one '*' argument is admitted"
      star := some (← `(starlark%[$value]))
    | `(starlarkArg| $identifier:ident = $value) =>
      if star.isSome then
        Macro.throwErrorAt arg "keyword arguments must precede '*'"
      let name ← quoteName identifier
      if names.contains name then
        Macro.throwErrorAt identifier s!"duplicate explicit keyword '{name}'"
      names := names.push name
      keywords := keywords.push (← `(($(Syntax.mkStrLit name), starlark%[$value])))
    | `(starlarkArg| $value:starlarkExpr) =>
      if !keywords.isEmpty || star.isSome then
        Macro.throwErrorAt arg "positional arguments must precede keywords and '*'"
      positional := positional.push (← `(starlark%[$value]))
    | _ => Macro.throwErrorAt arg "unsupported Starlark argument"
  let optionTerm (value : Option (TSyntax `term)) := match value with
    | none => `(none)
    | some value => `(some $value)
  `(Resolve.SourceExpr.call starlark%[$callee] [$[$positional],*] [$[$keywords],*]
      $(← optionTerm star) $(← optionTerm starStar))

private meta def quoteExpr (expression : TSyntax `starlarkExpr) : MacroM (TSyntax `term) :=
  match expression with
  | `(starlarkExpr| $identifier:ident) => do
    let name ← quoteName identifier
    `(Resolve.SourceExpr.scalar (.read $(Syntax.mkStrLit name)))
  | `(starlarkExpr| $literal:num) => do
    checkDecimal literal
    `(Resolve.SourceExpr.scalar (.int $literal))
  | `(starlarkExpr| $literal:str) => do
    let text := literal.getString
    unless literal.raw[0].getAtomVal == "\"" ++ text ++ "\"" &&
        !text.toList.any (fun c => c == '\\' || c == '\n' || c == '\r') do
      Macro.throwErrorAt literal "expected a double-quoted string without escapes"
    `(Resolve.SourceExpr.string $literal)
  | `(starlarkExpr| ($inner)) => `(starlark%[$inner])
  | `(starlarkExpr| -$value) => do
    let `(starlarkExpr| $literal:num) := value
      | Macro.throwErrorAt expression.raw[0] "unary '-' is admitted only on a decimal integer literal"
    checkDecimal literal
    `(Resolve.SourceExpr.scalar (.int (-$literal)))
  | `(starlarkExpr| $callee($args,*)) => quoteCall callee args.getElems
  | `(starlarkExpr| $left and $right) =>
    `(Resolve.SourceExpr.logical .and starlark%[$left] starlark%[$right])
  | `(starlarkExpr| $left or $right) =>
    `(Resolve.SourceExpr.logical .or starlark%[$left] starlark%[$right])
  | `(starlarkExpr| $yes if $test else $no) =>
    `(Resolve.SourceExpr.conditional starlark%[$test] starlark%[$yes] starlark%[$no])
  | `(starlarkExpr| $_ + $_) =>
    Macro.throwErrorAt expression.raw[1] "binary '+' is outside the Starlark expression quotation"
  | `(starlarkExpr| $_[$_]) =>
    Macro.throwErrorAt expression.raw[1] "subscripts are outside the Starlark expression quotation"
  | `(starlarkExpr| [$_args,*]) =>
    Macro.throwErrorAt expression.raw[0] "list displays are outside the Starlark expression quotation"
  | _ => Macro.throwErrorAt expression "unsupported Starlark expression"

macro_rules
  | `(starlark%[$expression]) => withRef expression (quoteExpr expression)

end Silmaril.Languages.Starlark.Functions.Lowering.Quote
