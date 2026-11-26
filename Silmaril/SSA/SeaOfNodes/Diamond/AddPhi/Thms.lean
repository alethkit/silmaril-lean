module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi

open Pure.SubZero (model)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : WordGraph inputs sigs} {rhs : WordWire inputs sigs} {target : Result inputs sigs}

/-- Successful rewrites keep the shared table, predicate and Region predecessors. -/
theorem rewrite?_keeps_control (accepted : rewrite? g rhs = some target) :
    target.shared = g.dataflow ∧ target.predicate = g.predicate ∧ target.merge = g.phi.merge :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.keeps_control accepted

/-- Each output arm implements the add at the same original predecessor occurrence. -/
theorem rewrite?_slot_eval_eq (accepted : rewrite? g rhs = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (target.arms slot).eval model entry (target.shared.eval model entry PUnit.unit) =
      .cons (sourceAt g rhs entry slot) .nil :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.slot_eval_eq accepted entry slot

/-- For every typed input, the taken predecessor returns the original modular sum. -/
theorem rewrite?_denote_eq (accepted : rewrite? g rhs = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    target.denote model entry = .cons (sourceDenote g rhs entry) .nil :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.denote_eq accepted entry

/-- The emitted native Diamond preserves and reflects the scoped finite return. -/
theorem rewrite?_returns_iff (accepted : rewrite? g rhs = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (result : BitVec 64) :
    target.Returns model entry (.cons result .nil) ↔ SourceReturns g rhs entry result :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.returns_iff accepted entry result

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi
