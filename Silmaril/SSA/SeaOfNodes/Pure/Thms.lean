module

public import Silmaril.SSA.SeaOfNodes.Pure.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.Correctness

/-! Correctness of the pure-value Sea of Nodes lowering at a single result. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Pure

open Diamond (Model Signature Val ValueSort dataPorts)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}

/-- The lowered graph returns the singleton tuple of the source result on every input. -/
theorem Program.lower_run (p : Program Op inputs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts inputs)) :
    p.lower.run (toRVSDGModel m) entry = .cons (p.eval m entry) .nil :=
  Proofs.lower_run p m entry

/-- Translating both sides preserves and reflects satisfaction in the induced model. -/
theorem Equation.satisfaction (e : Equation Op inputs out) (m : Model.{u, v, w} Op) :
    e.toRVSDG.Holds (toRVSDGModel m) ↔ e.Holds m :=
  Proofs.satisfaction e m

end Silmaril.SSA.SeaOfNodes.Pure
