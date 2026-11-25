module

public import Silmaril.Languages.Starlark.Functions.Comprehensions.Defs
public import Silmaril.Languages.Starlark.Functions.Lowering.Thms
public import Silmaril.Languages.Starlark.Functions.Thms
import Silmaril.Proofs.Languages.Starlark.Functions.Comprehensions.Lowering

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Comprehensions

open Lists (State Outcome)
open Lists.Iteration (Flow)

/-- The independent body rules give the exact native comprehension outcome,
including slot writes before a failed pattern node and iterator cleanup. -/
theorem exec_iff_denote (program : Program) (available : List DeclarationId)
    (comp : ListComp) (target : Binding) (state : State) (out : Outcome Flow) :
    Exec program available state (comp.body target) out ↔
      denoteBody program available (comp.body target) state = out :=
  exec_iff_denoteBody _ _ _ _ _

/-- Scratch-lowering every operand gives the exact native outcome and state.
Each staging scope restores the original direct bindings and lexical map on
both exits, so no scratch projection is needed at the end of the comprehension. -/
theorem lower_preserves (program : Program) (available : List DeclarationId)
    (comp : ListComp) (target : Binding) (state : State) (start : Nat := 0)
    (outer : Lowering.Admitted comp.iterable) (inner : ∀ expr ∈ comp.rest.operands, Lowering.Admitted expr)
    (locals : ∀ name ∈ comp.locals, ¬ Lowering.Scratch 0 name)
    (free : Lowering.ScratchFree state) :
    denoteBody program available (comp.lower target start) state =
      denoteBody program available (comp.body target) state :=
  Proofs.Languages.Starlark.Functions.Comprehensions.lower_preserves
    program available comp target state start outer inner locals free

end Silmaril.Languages.Starlark.Functions.Comprehensions
