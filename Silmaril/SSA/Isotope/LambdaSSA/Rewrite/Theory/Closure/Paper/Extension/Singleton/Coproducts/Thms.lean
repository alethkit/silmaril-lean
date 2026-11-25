module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionCoproducts

/-! # Copair and coproduct-map congruence after projection -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

/-- Case congruence respects equality after projecting each arm. -/
theorem projection_map_desc_congr {A B C : τ}
    {l l' : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType C} {r r' : Paper.TypeCategory.ofType (Φ := Φ) B ⟶ Paper.TypeCategory.ofType C}
    (hl : (projection Seed).map l = (projection Seed).map l')
    (hr : (projection Seed).map r = (projection Seed).map r') :
    (projection Seed).map (coprod.desc l r) = (projection Seed).map (coprod.desc l' r') :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionCoproducts.map_desc_congr Seed hl hr

/-- The image of a chosen Paper coproduct map depends only on the projected arms. -/
theorem projection_map_coprod_map_congr {A B C D : τ}
    {l l' : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType C} {r r' : Paper.TypeCategory.ofType (Φ := Φ) B ⟶ Paper.TypeCategory.ofType D}
    (hl : (projection Seed).map l = (projection Seed).map l')
    (hr : (projection Seed).map r = (projection Seed).map r') :
    (projection Seed).map (coprod.map l r) = (projection Seed).map (coprod.map l' r') :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionCoproducts.map_coprod_map_congr
    Seed hl hr

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
