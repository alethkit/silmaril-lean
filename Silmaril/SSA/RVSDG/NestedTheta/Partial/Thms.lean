module

public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Partial.Adequacy
import Silmaril.SSA.RVSDG.NestedTheta.Thms

/-! # Finite observations of partial nested graphs -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Partial

universe u v w
variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- A returned tuple is observed exactly when the graph has a finite derivation. -/
theorem observe_eq_some (m : Model.{u,v,w} Op) (g : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    observe m g input = Part.some output ↔ returns m g input output := by
  rw [Part.eq_some_iff]
  exact Proofs.mem_denoteOpen m g.toTerm input PUnit.unit output

/-- At total primitives, partial observation is exactly success of the
numbered evaluator at some finite bound. -/
theorem observe_ofRuntime_eq_some_iff_returns (m : RVSDG.Model.{u,v,w} Op)
    (g : Graph Op args [] sigs outs) (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    observe (MonadicModel.ofRuntime m) g input = Part.some output ↔ g.Returns m input output :=
  (observe_eq_some (MonadicModel.ofRuntime m) g input output).trans
    ((Proofs.returns_ofRuntime_iff m g input output).trans (g.returns_iff m input output).symm)

end Silmaril.SSA.RVSDG.NestedTheta.Partial
