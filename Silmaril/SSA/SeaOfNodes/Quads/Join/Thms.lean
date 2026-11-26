module

public import Silmaril.SSA.SeaOfNodes.Quads.Join.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Join.Correctness

/-! # Exact edge and return agreement for one closed quad join -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Join

open RVSDG (Tuple)
open Diamond (ValueSort Signature Model Val dataPorts Merge Projection)

universe u v w
variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

/-- Slot order associates each selected edge with its own If projection. -/
theorem predecessor_selected (merge : Merge) (condition : Bool) :
    merge.predecessor (selected merge condition) = Projection.ofBool condition :=
  Proofs.predecessor_selected merge condition

/-- The numbered child graph returns the independently computed incoming column. -/
theorem Program.arm_results (p : Program Op regs out) (i : Fin 2) :
    (p.arm i).toGraph.results = p.incoming (slotAt i) :=
  Proofs.arm_results p i

/-- Evaluating an incoming column delivers exactly that predecessor's final bank. -/
theorem Program.arm_run (p : Program Op regs out) (i : Fin 2) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) :
    (p.arm i).toGraph.run (model m) entry = (p.predecessor (slotAt i)).eval m entry :=
  Proofs.arm_graph_run p i m entry

/-- The numbered graph selects the corresponding predecessor and runs the join
with its typed arguments, returning the same value as ordered execution. -/
theorem Program.lower_run (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) :
    p.lower.run (model m) entry = .cons (p.eval m entry) .nil :=
  Proofs.lower_run p m entry

end Silmaril.SSA.SeaOfNodes.Quads.Join
