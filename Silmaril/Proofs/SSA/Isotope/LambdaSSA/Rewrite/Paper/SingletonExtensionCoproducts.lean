module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms

/-! # Copair congruence after projection to a contextual extension -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionCoproducts

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory Paper.Extension.Singleton
open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option backward.isDefEq.respectTransparency false in
theorem map_desc_congr {A B C : τ}
    {l l' : ofType (Φ := Φ) A ⟶ ofType C} {r r' : ofType (Φ := Φ) B ⟶ ofType C}
    (hl : (projection Seed).map l = (projection Seed).map l')
    (hr : (projection Seed).map r = (projection Seed).map r') :
    (projection Seed).map (coprod.desc l r) = (projection Seed).map (coprod.desc l' r') := by
  obtain ⟨_, el, rfl⟩ := exists_ofRegion l
  obtain ⟨_, el', rfl⟩ := exists_ofRegion l'
  obtain ⟨_, er, rfl⟩ := exists_ofRegion r
  obtain ⟨_, er', rfl⟩ := exists_ofRegion r'
  have left := (Paper.Extension.Singleton.ofRegion_eq_iff Seed el el').mp hl
  have right := (Paper.Extension.Singleton.ofRegion_eq_iff Seed er er').mp hr
  apply (cancel_epi ((projection Seed).map (sumIso A B).hom)).mp
  rw [← Functor.map_comp, ← Functor.map_comp, coprod_desc_ofRegion, coprod_desc_ofRegion]
  apply (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).mpr
  exact .case (.var (i := 0) rfl)
    (left.renameVars ((Ren.wk [] (Silmaril.coprod A B)).lift A))
    (right.renameVars ((Ren.wk [] (Silmaril.coprod A B)).lift B))

theorem map_coprod_map_congr {A B C D : τ}
    {l l' : ofType (Φ := Φ) A ⟶ ofType C} {r r' : ofType (Φ := Φ) B ⟶ ofType D}
    (hl : (projection Seed).map l = (projection Seed).map l')
    (hr : (projection Seed).map r = (projection Seed).map r') :
    (projection Seed).map (coprod.map l r) = (projection Seed).map (coprod.map l' r') := by
  have map_eq (f : ofType (Φ := Φ) A ⟶ ofType C) (g : ofType (Φ := Φ) B ⟶ ofType D) :
      coprod.map f g = coprod.desc (f ≫ coprod.inl) (g ≫ coprod.inr) := by
    apply coprod.hom_ext <;> simp
  rw [map_eq, map_eq]
  exact map_desc_congr Seed (by simp only [Functor.map_comp, hl])
    (by simp only [Functor.map_comp, hr])

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionCoproducts
