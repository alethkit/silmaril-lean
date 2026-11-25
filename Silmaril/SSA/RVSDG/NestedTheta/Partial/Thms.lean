module

public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Partial.Adequacy

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

end Silmaril.SSA.RVSDG.NestedTheta.Partial
