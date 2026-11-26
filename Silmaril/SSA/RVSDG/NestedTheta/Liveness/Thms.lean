module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Correct

public section

namespace Silmaril.SSA.RVSDG.NestedTheta

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- The executable sweep computes exactly the shared least may solution. -/
theorem Graph.mem_liveAt_iff (g : Graph Op args [] sigs outs) (pc : Nat) (a : Address) :
    a ∈ g.liveAt pc ↔ a ∈ g.liveness.mayOut pc :=
  Liveness.Proofs.liveAt_iff g pc a

/-- Agreement on the live entry ports preserves the entire bounded result. -/
theorem Graph.run_congr_of_live (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op) (fuel : Nat)
    (left right : Tuple m.Val args) (agree : g.AgreesOnLiveInputs left right) :
    g.run m fuel left = g.run m fuel right :=
  Liveness.Proofs.run_congr g m fuel left right agree

/-- The same agreement preserves every unbounded finite return, including
its returned state ports. -/
theorem Graph.returns_congr_of_live (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (left right : Tuple m.Val args) (agree : g.AgreesOnLiveInputs left right) (out : Tuple m.Val outs) :
    g.Returns m left out ↔ g.Returns m right out := by
  unfold Graph.Returns
  exact exists_congr fun fuel => by rw [g.run_congr_of_live m fuel left right agree]

end Silmaril.SSA.RVSDG.NestedTheta
