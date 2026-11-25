module

public import Silmaril.Languages.Starlark.Defs

public section

namespace Silmaril.Languages.Starlark

inductive StaticError where
  | undefinedName (name : String)
  | duplicateGlobal (name : String)
  | topLevelIf
  | topLevelReturn
  deriving DecidableEq, Repr

private def resolveName (locals globals : List String) (name : String) :
    Except StaticError Ref :=
  if locals.contains name then
    .ok (.bound ⟨.local, name⟩)
  else if globals.contains name then
    .ok (.bound ⟨.global, name⟩)
  else
    match name with
    | "None" => .ok (.predeclared .none)
    | "True" => .ok (.predeclared (.bool true))
    | "False" => .ok (.predeclared (.bool false))
    | _ => .error (.undefinedName name)

private def resolveExpr (name : String → Except StaticError Ref) :
    SourceExpr → Except StaticError ResolvedExpr
  | .int n => .ok (.int n)
  | .read x => return .read (← name x)
  | .unary op arg => return .unary op (← resolveExpr name arg)
  | .binary op lhs rhs => return .binary op (← resolveExpr name lhs) (← resolveExpr name rhs)
  | .logical op lhs rhs => return .logical op (← resolveExpr name lhs) (← resolveExpr name rhs)
  | .conditional test yes no =>
    return .conditional (← resolveExpr name test) (← resolveExpr name yes) (← resolveExpr name no)

private def resolveStmt (name : String → Except StaticError Ref) (scope : Scope) :
    SourceStmt → Except StaticError ResolvedStmt
  | .pass => .ok .pass
  | .eval expr => return .eval (← resolveExpr name expr)
  | .assign target rhs => return .assign ⟨scope, target⟩ (← resolveExpr name rhs)
  | .seq first rest =>
    return .seq (← resolveStmt name scope first) (← resolveStmt name scope rest)
  | .branch test yes no =>
    return .branch (← resolveExpr name test) (← resolveStmt name scope yes)
      (← resolveStmt name scope no)
  | .ret none => .ok (.ret none)
  | .ret (some value) => return .ret (some (← resolveExpr name value))

private def collectGlobals (seen : List String) : SourceStmt → Except StaticError (List String)
  | .assign name _ =>
    if seen.contains name then .error (.duplicateGlobal name) else .ok (name :: seen)
  | .seq first rest => do
    collectGlobals (← collectGlobals seen first) rest
  | .branch .. => .error .topLevelIf
  | .ret .. => .error .topLevelReturn
  | .pass | .eval _ => .ok seen

private def collectLocals (seen : List String) : SourceStmt → List String
  | .assign name _ => name :: seen
  | .seq first rest => collectLocals (collectLocals seen first) rest
  | .branch _ yes no => collectLocals (collectLocals seen yes) no
  | .pass | .eval _ | .ret _ => seen

/-- Validate a scalar module and resolve all reads, including forward references. -/
def resolveModule (body : SourceStmt) : Except StaticError ResolvedStmt := do
  let globals ← collectGlobals [] body
  resolveStmt (resolveName [] globals) .global body

/-- Resolve a function body in its lexical context, before choosing any control-flow path.
The parameter and global lists describe bindings supplied by the caller. -/
def resolveFunctionBody (globals parameters : List String) (body : SourceStmt) :
    Except StaticError ResolvedStmt :=
  resolveStmt (resolveName (collectLocals parameters body) globals) .local body

end Silmaril.Languages.Starlark
