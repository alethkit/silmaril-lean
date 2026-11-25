module

public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Isomorphism.Invariance

public section

namespace Silmaril.SSA.RVSDG.NestedTheta

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {sigs sigs' : List (Ports (PortType V S))}
variable {left : Graph Op args [] sigs outs} {right : Graph Op args [] sigs' outs}

/-- Typed hierarchical renumbering preserves the full result at each θ bound. -/
theorem Graph.Isomorphic.run_eq (iso : Graph.Isomorphic Op left right)
    (m : Model.{u, v, w} Op) (fuel : Nat) (entry : Tuple m.Val args) :
    left.run m fuel entry = right.run m fuel entry :=
  Isomorphism.Proofs.run_eq iso m fuel entry

/-- Renumbering preserves both directions of the graph's finite-return observation. -/
theorem Graph.Isomorphic.returns_iff (iso : Graph.Isomorphic Op left right)
    (m : Model.{u, v, w} Op) (entry : Tuple m.Val args) (output : Tuple m.Val outs) :
    left.Returns m entry output ↔ right.Returns m entry output := by
  simp only [Graph.Returns, iso.run_eq m]

/-- Renumbering preserves unbounded finite-return observations for the decoded terms. -/
theorem Graph.Isomorphic.term_returns_iff (iso : Graph.Isomorphic Op left right)
    (m : Model.{u, v, w} Op) (entry : Tuple m.Val args) (output : Tuple m.Val outs) :
    left.toTerm.Returns m entry output ↔ right.toTerm.Returns m entry output := by
  rw [← left.returns_iff, ← right.returns_iff, iso.returns_iff]

end Silmaril.SSA.RVSDG.NestedTheta
