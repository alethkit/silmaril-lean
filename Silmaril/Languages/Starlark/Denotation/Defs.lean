module

public import Silmaril.Languages.Starlark.Resolve.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark

/-- Compose scalar meanings in source evaluation order. -/
def denoteExpr : ResolvedExpr → Frame → Result Value
  | .int value, _ => .ok (.int value)
  | .read ref, frame => frame.read ref
  | .unary op arg, frame => do
    applyUnary op (← denoteExpr arg frame)
  | .binary op left right, frame => do
    let lhs ← denoteExpr left frame
    let rhs ← denoteExpr right frame
    applyBinary op lhs rhs
  | .logical op left right, frame => do
    let lhs ← denoteExpr left frame
    if op.runsRight lhs then denoteExpr right frame else .ok lhs
  | .conditional test yes no, frame => do
    let value ← denoteExpr test frame
    if value.truth then denoteExpr yes frame else denoteExpr no frame

/-- A scalar suite transforms bindings until the first return or dynamic failure. -/
def denoteStmt : ResolvedStmt → Frame → Result Completion
  | .pass, frame => .ok ⟨frame, none⟩
  | .eval expr, frame => do
    let _ ← denoteExpr expr frame
    return ⟨frame, none⟩
  | .assign name rhs, frame => do
    let value ← denoteExpr rhs frame
    return ⟨frame.write name value, none⟩
  | .seq first rest, frame => do
    let result ← denoteStmt first frame
    match result.returned with
    | some _ => return result
    | none => denoteStmt rest result.frame
  | .branch test yes no, frame => do
    let value ← denoteExpr test frame
    if value.truth then denoteStmt yes frame else denoteStmt no frame
  | .ret none, frame => .ok ⟨frame, some .none⟩
  | .ret (some value), frame => do
    let result ← denoteExpr value frame
    return ⟨frame, some result⟩

inductive Failure where
  | static (error : StaticError)
  | dynamic (error : RuntimeError)
  deriving DecidableEq, Repr

/-- Initialize a closed scalar module and return its global bindings on success. -/
def runModule (body : SourceStmt) : Except Failure Bindings := do
  let code ← (resolveModule body).mapError .static
  let result ← (denoteStmt code {}).mapError .dynamic
  return result.frame.globals

/-- Execute a body with already bound scalar globals and parameters.
The first entry for a name supplies its value. Falling through returns Starlark `None`. -/
def runFunctionBody (globals parameters : List (String × Value)) (body : SourceStmt) :
    Except Failure Value := do
  let code ← (resolveFunctionBody (globals.map Prod.fst) (parameters.map Prod.fst) body).mapError
    .static
  let frame : Frame :=
    { locals := fun name => List.lookup name parameters
      globals := fun name => List.lookup name globals }
  let result ← (denoteStmt code frame).mapError .dynamic
  return result.returned.getD .none

end Silmaril.Languages.Starlark
