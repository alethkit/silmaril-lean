module

public import Silmaril.SSA.RVSDG.Petri.Defs
import Silmaril.Proofs.SSA.RVSDG.Petri.Adequacy

/-! Finite completed firing sequences and numbered evaluation agree. -/

public section

namespace Silmaril.SSA.RVSDG.Petri

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- A marking that can still fire has no completed region observation. -/
theorem step_unfinished (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) {before after : GraphMarking m graph}
    (step : Step m graph input before after) : result m graph input before = none :=
  Proofs.fire_unfinished m step

/-- Every completed legal schedule returns the numbered evaluation result, and
that result is reached by some finite schedule. -/
theorem finishes_iff (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    Finishes m graph input output ↔ graph.run m input = output :=
  ⟨Proofs.sound m graph input, fun h => h ▸ Proofs.complete m graph input⟩

end Silmaril.SSA.RVSDG.Petri
