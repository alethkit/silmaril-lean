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

/-- Bounded execution at zero θ budget is sound and complete for the
independent inductive relation over calls, primitive nodes and selected γ arms. -/
theorem call_iff (m : Machine.{u, v, w} Op) (callee : m.Val (.value (.function args outs)))
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    Returns m (.call callee input) output ↔ ∃ depth, invoke m 0 depth callee input = some output :=
  Proofs.call_iff m callee input output

/-- A finite derivation has a sufficient call depth that succeeds at all larger depths. -/
theorem returns_eventually (m : Machine.{u, v, w} Op) {job : Job m outs} {output : Tuple m.Val outs}
    (derivation : Returns m job output) :
    ∃ depth, ∀ bound, depth ≤ bound → job.run m bound = some output :=
  Proofs.complete m derivation

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive
