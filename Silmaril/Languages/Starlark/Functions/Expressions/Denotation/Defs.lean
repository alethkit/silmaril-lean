module

public import Silmaril.Languages.Starlark.Functions.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (Meaning Outcome)
open Lists.Iteration (Flow truth)

/-- Execute the body of a prepared closure. -/
abbrev ClosureMeaning (available : List DeclarationId) := Prepared available → Meaning Flow

/-- Interpret a prepared closure by the supplied body denotation. Restore the
caller bindings on both exits and retain the state left by the callee. -/
def denoteDispatchWith (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available)
    (callee : Lists.Value) (actual : Actual) : Meaning Lists.Value :=
  fun caller =>
    match prepareExpanded program available actual callee caller with
    | .error error next => .error error next
    | .ok (.builtin id args) next => Builtins.invoke id args next
    | .ok (.closure plan) next =>
      match bodyMeaning plan next with
      | .ok flow final => .ok (callValue flow) (restoreCaller caller final)
      | .error error final => .error error (restoreCaller caller final)

/-- Apply an evaluated callee and operands, with expansion before dispatch. -/
def denoteApplicationWith (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available)
    (shape : ArgumentShape) : List Lists.Value → Meaning Lists.Value
  | [] => throw .notCallable
  | callee :: operands => do
    let actual ← (shape.collect operands).expand
    denoteDispatchWith program available bodyMeaning callee actual

/-- Finish each insertion before starting the next key. -/
def denoteEntries (receiver : Lists.Value) : List (Meaning Lists.Value × Meaning Lists.Value) → Meaning Unit
  | [] => pure ()
  | (key, value) :: rest => fun state =>
    Outcome.resume (key state) fun k next =>
    Outcome.resume (value next) fun v inserted =>
    Outcome.resume (Lists.insertDisplayEntry receiver k v inserted) fun _ => denoteEntries receiver rest

/-- Interpret resolved expressions in syntax order. Calls delegate their
prepared closure bodies to the supplied denotation. -/
def denoteExprWith (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) : Expr → Meaning Lists.Value
  | .atom code => Lists.denote code
  | .list elements => fun state =>
    let values := elements.attach.mapM fun element => do
      have := List.sizeOf_lt_of_mem element.property
      denoteExprWith program available bodyMeaning element.val
    Outcome.resume (values state) Lists.allocate
  | .tuple elements => fun state =>
    let values := elements.attach.mapM fun element => do
      have := List.sizeOf_lt_of_mem element.property
      denoteExprWith program available bodyMeaning element.val
    Outcome.resume (values state) Lists.allocateTuple
  | .dict entries => fun state =>
    let actions := entries.attach.map fun ⟨(key, value), member⟩ =>
      have := (entrySize member).1
      have := (entrySize member).2
      (denoteExprWith program available bodyMeaning key,
        denoteExprWith program available bodyMeaning value)
    Outcome.resume (Lists.allocateDict [] state) fun receiver next =>
      Outcome.resume (denoteEntries receiver actions next) fun _ => pure receiver
  | .index receiver subscript => fun state =>
    Outcome.resume (denoteExprWith program available bodyMeaning receiver state) fun value next =>
      Outcome.resume (denoteExprWith program available bodyMeaning subscript next) (Lists.readIndex value)
  | .call callee positional keywords star starStar => do
    let callable ← denoteExprWith program available bodyMeaning callee
    let values ← (argumentExprs positional keywords star starStar).attach.mapM fun operand => do
      have := argumentSize callee positional keywords star starStar operand.property
      denoteExprWith program available bodyMeaning operand.val
    denoteApplicationWith program available bodyMeaning (argumentShape positional keywords star starStar) (callable :: values)
  | .branch test yes no => do
    let flag ← truth (← denoteExprWith program available bodyMeaning test)
    if flag then denoteExprWith program available bodyMeaning yes else denoteExprWith program available bodyMeaning no
  | .logical op left right => do
    let value ← denoteExprWith program available bodyMeaning left
    let flag ← truth value
    if (if op = .and then flag else !flag) then denoteExprWith program available bodyMeaning right else pure value
termination_by expression => sizeOf expression
decreasing_by all_goals first | assumption | (simp_wf; omega)

end Silmaril.Languages.Starlark.Functions.Lowering
