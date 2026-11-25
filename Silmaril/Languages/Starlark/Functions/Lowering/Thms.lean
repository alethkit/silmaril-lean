module

public import Silmaril.Languages.Starlark.Functions.Lowering.Source.Defs
public import Silmaril.Languages.Starlark.Functions.Denotation.Defs
import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Preservation

public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (State Outcome)

/-- Compile a resolved source derivation for atoms, list displays, subscript
reads, calls with positional, named and spread operands, and conditional or
short-circuit expressions. Success
commits the source value to the destination. Both exits preserve the source
state up to direct scratch bindings, including the exact heap, lexical slot
map and iterator stack. -/
theorem lower_preserves {program : Program} {available : List DeclarationId} {state : State}
    {expression : Expr} {out : Outcome Lists.Value} (ran : Evaluates program available state expression out)
    (free : ScratchFree state) (destination : Binding) (visible : ¬ Scratch 0 destination)
    (start : Nat := 0) :
    match out with
    | .ok value s => ∃ targetState,
        denoteBody program available (lower expression destination start).code state = .ok .next targetState ∧
        StateMatch 0 (s.write destination value) targetState
    | .error error s => ∃ targetState,
        denoteBody program available (lower expression destination start).code state = .error error targetState ∧
        StateMatch 0 s targetState :=
  Proofs.Languages.Starlark.Functions.Lowering.preserves ran free destination visible start

/-- Projection preserves lookup on visible names, including uninitialized reads. -/
theorem StateMatch.bindingValue_eq {i : Nat} {s t : State} (h : StateMatch i s t) {name : Binding}
    (visible : ¬ Scratch i name) : t.bindingValue name = s.bindingValue name :=
  Proofs.Languages.Starlark.Functions.Lowering.read_match h visible

end Silmaril.Languages.Starlark.Functions.Lowering
