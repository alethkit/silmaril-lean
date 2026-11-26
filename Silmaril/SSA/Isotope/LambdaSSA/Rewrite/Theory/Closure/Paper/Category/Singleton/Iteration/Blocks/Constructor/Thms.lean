module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Blocks.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ConstructorBlockUniformity

/-! # Native uniformity for separate constructor maps on two blocks -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ

/-- Bekić elimination in the chosen coproduct coordinates. -/
theorem iterate_coprod_rows {A D B : P}
    (left : A ⟶ (B ⨿ A) ⨿ D) (right : D ⟶ (B ⨿ A) ⨿ D) :
    let tail := iterate right
    let head := iterate (left ≫ coprod.desc (𝟙 (B ⨿ A)) tail)
    iterate (coprod.desc left right ≫ (coprod.associator B A D).hom) =
      coprod.desc head (tail ≫ coprod.desc (𝟙 B) head) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ConstructorBlockUniformity.iterate_coprod_rows left right

/-- A state map that applies separate constructor returns in two summands
is native-uniform. Both blocks may exit, recur, or transfer to the other block. -/
theorem iterate_uniformity_of_coprod_constructor {A C D E B : P}
    {h : A ⟶ C} {k : D ⟶ E} (hh : ConstructorReturn h) (hk : ConstructorReturn k)
    (f : A ⨿ D ⟶ B ⨿ (A ⨿ D)) (g : C ⨿ E ⟶ B ⨿ (C ⨿ E))
    (square : f ≫ coprod.map (𝟙 B) (coprod.map h k) = coprod.map h k ≫ g) :
    iterate f = coprod.map h k ≫ iterate g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ConstructorBlockUniformity.iterate_uniformity hh hk f g square

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
