module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtension

/-! # Exact arrows and whiskering in an extended singleton quotient -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory
open Silmaril.Isotope.LambdaSSA (VCtx LCtx)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

instance homCongruence : Congruence (homRel Seed) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtension.congruence

/-- The quotient identifies exactly the extended equations on singleton
representatives. -/
theorem ofRegion_eq_iff {A B : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B]) :
    ofRegion Seed hr = ofRegion Seed hs ↔ Extension.Eqv Seed [A] r s [B] :=
  (CategoryTheory.Quotient.functor_map_eq_iff (homRel Seed) _ _).trans
    (Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtension.homRel_ofRegion_iff hr hs)

theorem homRel_whiskerLeft (X : Paper.TypeCategory (τ := τ) Φ)
    {Y Z : Paper.TypeCategory (τ := τ) Φ} {f g : Y ⟶ Z} (h : homRel Seed f g) :
    homRel Seed (Paper.TypeCategory.whiskerLeft X f) (Paper.TypeCategory.whiskerLeft X g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtension.whiskerLeft_congr X h

/-- Left whiskering descends from the old category to the quotient. -/
@[expose] def whiskerLeftFunctor (X : TypeCategory Seed) : TypeCategory Seed ⥤ TypeCategory Seed :=
  CategoryTheory.Quotient.lift (homRel Seed) (Paper.TypeCategory.whiskerLeftFunctor X.as ⋙ projection Seed)
    (fun _ _ _ _ h => CategoryTheory.Quotient.sound (homRel Seed)
      (homRel_whiskerLeft Seed X.as h))

theorem whiskerLeft_map {X Y Z : Paper.TypeCategory (τ := τ) Φ} (f : Y ⟶ Z) :
    (whiskerLeftFunctor Seed ((projection Seed).obj X)).map ((projection Seed).map f) =
      (projection Seed).map (Paper.TypeCategory.whiskerLeft X f) := rfl

theorem whiskerRight_map_congr (X : Paper.TypeCategory (τ := τ) Φ)
    {Y Z : Paper.TypeCategory (τ := τ) Φ} {f g : Y ⟶ Z} (h : homRel Seed f g) :
    (projection Seed).map (Paper.TypeCategory.whiskerRight f X) =
      (projection Seed).map (Paper.TypeCategory.whiskerRight g X) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtension.whiskerRight_map_congr X h

/-- Right whiskering descends by the guarded braid and left-whiskering congruence. -/
@[expose] def whiskerRightFunctor (X : TypeCategory Seed) : TypeCategory Seed ⥤ TypeCategory Seed :=
  CategoryTheory.Quotient.lift (homRel Seed) (Paper.TypeCategory.whiskerRightFunctor X.as ⋙ projection Seed)
    (fun _ _ _ _ h => whiskerRight_map_congr Seed X.as h)

theorem whiskerRight_map {X Y Z : Paper.TypeCategory (τ := τ) Φ} (f : Y ⟶ Z) :
    (whiskerRightFunctor Seed ((projection Seed).obj X)).map ((projection Seed).map f) =
      (projection Seed).map (Paper.TypeCategory.whiskerRight f X) := rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
