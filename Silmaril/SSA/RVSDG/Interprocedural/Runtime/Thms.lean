module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Linking
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Invocation

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args outs : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}

/-- Both presentations link to exactly the same export tuple, including captured values,
closure bodies and initialized global identities. -/
theorem link_toGraph (m : Machine.{u, v, w} Op) (unitId : Nat)
    (term : OmegaTerm Op args outs sigs) (imports : Tuple m.Val args) :
    linkGraph m unitId term.toGraph imports = linkTerm m unitId term imports :=
  Proofs.linkBindings_eq m unitId imports term.region PUnit.unit

theorem link_toTerm (m : Machine.{u, v, w} Op) (unitId : Nat)
    (graph : Omega Op args outs sigs) (imports : Tuple m.Val args) :
    linkTerm m unitId graph.toTerm imports = linkGraph m unitId graph imports := by
  rw [← link_toGraph, graph.toGraph_toTerm]

/-- Linking is total on the φ-free fragment, for every total primitive machine
and supplied import tuple. -/
theorem links_iff_noPhi (m : Machine.{u, v, w} Op) (unitId : Nat)
    (term : OmegaTerm Op args outs sigs) (imports : Tuple m.Val args) :
    (∃ exports, linkTerm m unitId term imports = some exports) ↔ NoPhi term.region :=
  Proofs.links_iff m unitId imports term.region PUnit.unit

/-- A successful invocation returns the same tuple at any larger call and θ bounds. -/
theorem invoke_mono (m : Machine.{u, v, w} Op)
    {loops loops' calls calls' : Nat} (enoughLoops : loops ≤ loops') (enoughCalls : calls ≤ calls')
    (callee : m.Val (.value (.function args outs))) (input : Tuple m.Val args) (output : Tuple m.Val outs)
    (returns : invoke m loops calls callee input = some output) :
    invoke m loops' calls' callee input = some output :=
  Proofs.invoke_mono m enoughLoops calls calls' enoughCalls callee input output returns

end Silmaril.SSA.RVSDG.Interprocedural.Runtime
