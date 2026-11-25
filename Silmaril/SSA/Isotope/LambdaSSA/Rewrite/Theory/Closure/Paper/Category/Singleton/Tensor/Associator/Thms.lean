module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Associator.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardedAssociator

/-! # The guarded associator and its left- and middle-factor comparisons -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local infixr:70 " ×ₜ " => product

/-- Reassociate and expand the original product shape. -/
theorem associate_unassociate (A B C : τ) :
    associate (Φ := Φ) A B C ≫ unassociate A B C = 𝟙 (Obj ((A ×ₜ B) ×ₜ C)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardedAssociator.associate_unassociate A B C

/-- Expand and reassociate to the original product shape. -/
theorem unassociate_associate (A B C : τ) :
    unassociate (Φ := Φ) A B C ≫ associate A B C = 𝟙 (Obj (A ×ₜ B ×ₜ C)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardedAssociator.unassociate_associate A B C

/-- The guarded reassociation and its inverse are an isomorphism in default Paper. -/
@[expose] def associateIso (A B C : τ) : Obj ((A ×ₜ B) ×ₜ C) ≅ Obj (A ×ₜ B ×ₜ C) where
  hom := associate A B C
  inv := unassociate A B C
  hom_inv_id := associate_unassociate A B C
  inv_hom_id := unassociate_associate A B C

/-- The leftmost computation can run before or after guarded reassociation. -/
theorem associate_whiskerRight_right {A B : τ} (X Y : τ) (f : Obj A ⟶ Obj B) :
    whiskerRight (whiskerRight f (Obj X)) (Obj Y) ≫ associate B X Y =
      associate A X Y ≫ whiskerRight f (Obj (X ×ₜ Y)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardedAssociator.associate_whiskerRight_right X Y f

/-- The middle computation can run before or after guarded reassociation. -/
theorem associate_whiskerLeft_right {A B : τ} (X Y : τ) (f : Obj A ⟶ Obj B) :
    whiskerRight (whiskerLeft (Obj X) f) (Obj Y) ≫ associate X B Y =
      associate X A Y ≫ whiskerLeft (Obj X) (whiskerRight f (Obj Y)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardedAssociator.associate_whiskerLeft_right X Y f

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
