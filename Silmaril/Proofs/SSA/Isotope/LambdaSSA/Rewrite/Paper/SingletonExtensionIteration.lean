module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms

/-! # Transport singleton feedback through a contextual extension -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionIteration

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open SyntacticCategory (iterateRegion iterationBody iterationDispatch_valueBranches iterateRegion_valueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) {A B : τ}

set_option backward.isDefEq.respectTransparency false in
theorem iterateRegion_congr {p q : Region Φ}
    (hp : ValueBranches [A] p [Silmaril.coprod B A])
    (hq : ValueBranches [A] q [Silmaril.coprod B A])
    (e : Paper.Extension.Eqv Seed [A] p q [Silmaril.coprod B A]) :
    Paper.Extension.Eqv Seed [A] (iterateRegion A p) (iterateRegion A q) [B] := by
  have body : Paper.Extension.Eqv Seed [A] (iterationBody p) (iterationBody q) [A, B] :=
    e.lsubstPost hp hq (fun _ _ hi => by
      cases List.mem_singleton.mp (List.mem_of_getElem? hi)
      exact (iterationDispatch_valueBranches A B).hasType)
  exact .cfg (fun _ : Fin 1 => A)
    (.refl (.br (ℓ := 0) rfl (.var (i := 0) rfl)))
    (fun _ => body.renameVars ((Ren.wk [] A).lift A))

set_option backward.isDefEq.respectTransparency false in
theorem iterateSum_map_congr {f g : Paper.TypeCategory.ofType (Φ := Φ) A ⟶
    Paper.TypeCategory.ofType (Silmaril.coprod B A)}
    (h : (projection Seed).map f = (projection Seed).map g) :
    (projection Seed).map (Paper.TypeCategory.iterateSum f) =
      (projection Seed).map (Paper.TypeCategory.iterateSum g) := by
  obtain ⟨_, hp, rfl⟩ := Paper.TypeCategory.exists_ofRegion f
  obtain ⟨_, hq, rfl⟩ := Paper.TypeCategory.exists_ofRegion g
  rw [Paper.TypeCategory.iterateSum_ofRegion, Paper.TypeCategory.iterateSum_ofRegion]
  exact (ofRegion_eq_iff Seed (iterateRegion_valueBranches hp) (iterateRegion_valueBranches hq)).2
    (iterateRegion_congr Seed hp hq ((ofRegion_eq_iff Seed hp hq).1 h))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionIteration
