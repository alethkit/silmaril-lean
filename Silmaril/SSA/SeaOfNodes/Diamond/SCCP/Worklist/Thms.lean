module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Correctness

/-! Queue exhaustion and exact agreement with simultaneous SCCP. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}
variable (m : Model.{u, v, w} Op) [DecidableEq (sortValue m.value out)]
variable (g : Graph Op inputs sigs out) (entry : Tuple (Fact m.value) (dataPorts inputs))

theorem step_decreases (task : Task) (state : State m.value sigs out) (pending : List Task) :
    potential (step m g entry task state pending).2 < potential (task :: pending) :=
  Proofs.step_decreases task state pending

/-- The certified queue budget always suffices to process all pending work. -/
theorem run_drains : (run m g entry).pending = [] :=
  Proofs.run_drains

/-- The entire typed assignment agrees with bounded simultaneous iteration. -/
theorem solve_eq_simultaneous : solve m g entry = SCCP.solve m g entry :=
  Proofs.solve_eq_simultaneous

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist
