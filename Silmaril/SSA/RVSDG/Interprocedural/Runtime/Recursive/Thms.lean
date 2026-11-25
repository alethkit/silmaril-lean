module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Recursive

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args outs : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}

/-- The two linkers produce identical typed exports, including φ member references. -/
theorem link_toGraph (m : Machine.{u, v, w} Op) (unitId : Nat) (term : OmegaTerm Op args outs sigs)
    (imports : Tuple m.Val args) : linkGraph m unitId term.toGraph imports = linkTerm m unitId term imports :=
  Proofs.linkBindings_eq m unitId imports term.region PUnit.unit

/-- Bounded execution is sound and complete for the independent finite
relation over calls, primitive nodes, selected γ arms and θ iterations. -/
theorem call_iff (m : Machine.{u, v, w} Op) (callee : m.Val (.value (.function args outs)))
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    Returns m (.call callee input) output ↔ ∃ loops depth, invoke m loops depth callee input = some output :=
  Proofs.call_iff m callee input output

/-- Each finite derivation succeeds at all sufficiently large call and per-θ bounds. -/
theorem returns_eventually (m : Machine.{u, v, w} Op) {job : Job m outs} {output : Tuple m.Val outs}
    (derivation : Returns m job output) :
    ∃ callLimit loopLimit, ∀ loops depth, callLimit ≤ depth → loopLimit ≤ loops →
      job.run m loops depth = some output :=
  Proofs.complete m derivation

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive
