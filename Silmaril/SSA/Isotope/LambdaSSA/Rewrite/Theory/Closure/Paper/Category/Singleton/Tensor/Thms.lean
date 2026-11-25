module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonTensor

/-! # Functorial whiskering in the singleton paper category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ

theorem whiskerLeft_id (X Y : Comp) :
    whiskerLeft X (𝟙 Y) = 𝟙 (tensorObj X Y) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonTensor.whiskerLeft_id X Y

theorem whiskerRight_id (X Y : Comp) :
    whiskerRight (𝟙 Y) X = 𝟙 (tensorObj Y X) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonTensor.whiskerRight_id X Y

theorem whiskerLeft_comp (X : Comp) {A B C : Comp} (f : A ⟶ B) (g : B ⟶ C) :
    whiskerLeft X (f ≫ g) = whiskerLeft X f ≫ whiskerLeft X g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonTensor.whiskerLeft_comp X f g

theorem whiskerRight_comp (X : Comp) {A B C : Comp} (f : A ⟶ B) (g : B ⟶ C) :
    whiskerRight (f ≫ g) X = whiskerRight f X ≫ whiskerRight g X :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonTensor.whiskerRight_comp X f g

/-- Product with a fixed left factor acts functorially on computations. -/
@[expose] def whiskerLeftFunctor (X : Comp) : Comp ⥤ Comp where
  obj := tensorObj X
  map := whiskerLeft X
  map_id := whiskerLeft_id X
  map_comp := whiskerLeft_comp X

/-- Product with a fixed right factor acts functorially on computations. -/
@[expose] def whiskerRightFunctor (X : Comp) : Comp ⥤ Comp where
  obj Y := tensorObj Y X
  map f := whiskerRight f X
  map_id := whiskerRight_id X
  map_comp := whiskerRight_comp X

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
