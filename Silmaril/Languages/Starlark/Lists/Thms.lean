module

public import Silmaril.Languages.Starlark.Lists.Denotation.Defs
public import Silmaril.Languages.Starlark.Lists.Freeze.Defs
public import Silmaril.Languages.Starlark.Lists.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.Eval
import Silmaril.Proofs.Languages.Starlark.Lists.Freeze

public section

namespace Silmaril.Languages.Starlark.Lists

/-- Evaluation agrees with the denotation on both success and failure states. -/
theorem eval_iff_denote {α : Type} (code : Code α) (state : State) (out : Outcome α) :
    Eval state code out ↔ denote code state = out :=
  ⟨Proofs.Languages.Starlark.Lists.denote_eq_of_eval,
    fun h => h ▸ Proofs.Languages.Starlark.Lists.eval_denote code state⟩

/-- Freezing is the unique pointwise update prescribed by live graph reachability. -/
theorem freezes_iff_freeze (heap : Heap) (roots : List Address) (after : Heap) :
    Freezes heap roots after ↔ heap.freeze roots = after :=
  ⟨Proofs.Languages.Starlark.Lists.eq_freeze_of_freezes,
    fun h => h ▸ Proofs.Languages.Starlark.Lists.freezes_freeze heap roots⟩

/-- A frozen cell rejects validated edits. Validation itself may report an earlier error. -/
theorem updateCell_frozen (state : State) (address : Address)
    (edit : List Value → Except Error (List Value)) {cell : Cell}
    (found : state.heap[address]? = some cell) (frozen : cell.frozen = true) :
    updateCell address edit state =
      match edit cell.elements with
      | .ok _ => .error (.frozen address) state
      | .error error => .error error state :=
  Proofs.Languages.Starlark.Lists.updateCell_frozen state address edit found frozen

end Silmaril.Languages.Starlark.Lists
