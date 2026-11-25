module

public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Partial.Isomorphism.Transport

/-! # Transport of partial observations along typed graph renumbering -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Partial

universe u v w
variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {args outs : Ports (PortType V S)} {sigs sigs' : List (Ports (PortType V S))}
variable {left : Graph Op args [] sigs outs} {right : Graph Op args [] sigs' outs}

/-- The entire partial observation is invariant under typed renumbering,
including when a selected primitive is undefined. -/
theorem observe_iso (iso : Graph.Isomorphic Op left right) (m : Model.{u,v,w} Op)
    (input : Tuple m.Val args) : observe m left input = observe m right input :=
  Isomorphism.Proofs.observe_eq m iso input

theorem returns_iso_iff (iso : Graph.Isomorphic Op left right) (m : Model.{u,v,w} Op)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    returns m left input output ↔ returns m right input output := by
  rw [← observe_eq_some, ← observe_eq_some, observe_iso iso]

end Silmaril.SSA.RVSDG.NestedTheta.Partial
