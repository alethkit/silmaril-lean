module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

theorem linkBindings_eq (m : Machine.{u, v, w} Op) (unitId : Nat) (imports : Tuple m.Val args)
    (term : ModuleTerm Op args past sigs outs) (locals : Locals m.Val past) :
    linkTable m unitId imports past sigs locals term.vertices term.results =
      linkBindings m unitId imports term locals := by
  induction term with
  | ret => rfl
  | bind definition rest ih =>
    simp only [ModuleTerm.vertices, ModuleTerm.results, linkTable, linkBindings]
    congr 1
    funext value
    apply ih

theorem links_iff (m : Machine.{u, v, w} Op) (unitId : Nat) (imports : Tuple m.Val args)
    (term : ModuleTerm Op args past sigs outs) (locals : Locals m.Val past) :
    (∃ exports, linkBindings m unitId imports term locals = some exports) ↔ NoPhi term := by
  induction term with
  | ret =>
    constructor
    · intro _; trivial
    · intro _; exact ⟨_, rfl⟩
  | bind definition rest ih =>
    cases definition with
    | lambda lambda =>
      change (∃ exports, linkBindings m unitId imports rest
        (locals.snoc (.cons (.closure
          (Lambda.close Op lambda.toGraph imports locals).values (Lambda.close Op lambda.toGraph imports locals).body)
          .nil)) = some exports) ↔ NoPhi rest
      apply ih
    | delta delta =>
      simp only [linkBindings, VertexTerm.toGraph, linkVertex, NoPhi]
      exact ih _
    | phi phi =>
      simp [linkBindings, VertexTerm.toGraph, linkVertex, NoPhi]

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Proofs
