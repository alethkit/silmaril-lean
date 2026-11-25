module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Strength.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Strength
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StrengthComparison

/-! # Iteration strength in the Paper singleton category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open CfgEta.TypeCategory (whiskerLeftRegion)
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)
open SyntacticCategory (iterateRegion)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ}

local notation "Comp" => TypeCategory (τ := τ) Φ

/-- Thread a retained variable through the CFG for a guarded singleton step.
The producer can contain effects and nested CFGs. -/
theorem whiskerLeftRegion_iterate (X : τ) {p : Region Φ}
    (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    Paper.Eqv [Silmaril.product X A]
      (whiskerLeftRegion (iterateRegion A p))
      (iterateRegion (Silmaril.product X A)
        (compLSubst (fun _ => whiskerLeftRegion p) (fun _ => distributorRegion) 0))
      [Silmaril.product X B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Strength.whiskerLeftRegion_iterate X hp

/-- The same representative equation after binding effectful branch arguments. -/
theorem whiskerLeftRegion_iterate_afterBinding (X : τ) {p : Region Φ}
    (hp : HasType [A] p [Silmaril.coprod B A]) :
    Paper.Eqv [Silmaril.product X A]
      (whiskerLeftRegion (iterateRegion A p.bindBranchArguments))
      (iterateRegion (Silmaril.product X A)
        (compLSubst (fun _ => whiskerLeftRegion p.bindBranchArguments) (fun _ => distributorRegion) 0))
      [Silmaril.product X B] :=
  whiskerLeftRegion_iterate X hp.bindBranchArguments

/-- Iteration strength when the step returns the exact syntactic sum. -/
theorem whiskerLeft_iterateSum (X : τ)
    (f : ofType (Φ := Φ) A ⟶ ofType (Silmaril.coprod B A)) :
    whiskerLeft (τ := τ) (ofType X) (iterateSum f) =
      iterateSum (A := Silmaril.product X A) (B := Silmaril.product X B)
        (whiskerLeft (τ := τ) (ofType X) f ≫ ofRegion (τ := τ) (distributorRegion_typed X B A)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Strength.whiskerLeft_iterateSum X f

/-- The canonical comparison for the fixed-left-factor functor is invertible.
Its inverse is the literal distributor transported to the chosen coproducts. -/
noncomputable def leftCoproductComparisonIso (Z X Y : Comp) :
    tensorObj Z X ⨿ tensorObj Z Y ≅ tensorObj Z (X ⨿ Y) where
  hom := coprodComparison (whiskerLeftFunctor Z) X Y
  inv := leftCoproductDistributor Z X Y
  hom_inv_id := Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StrengthComparison.comparison_hom_inv_id Z X Y
  inv_hom_id := Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StrengthComparison.comparison_inv_hom_id Z X Y

@[simp] theorem leftCoproductComparisonIso_hom (Z X Y : Comp) :
    (leftCoproductComparisonIso Z X Y).hom = coprodComparison (whiskerLeftFunctor Z) X Y := by
  unfold leftCoproductComparisonIso
  rfl

@[simp] theorem leftCoproductComparisonIso_inv (Z X Y : Comp) :
    (leftCoproductComparisonIso Z X Y).inv = leftCoproductDistributor Z X Y := by
  unfold leftCoproductComparisonIso
  rfl

/-- Iteration commutes with left whiskering after distributing over the chosen coproduct. -/
theorem whiskerLeft_iterate (Z : Comp) {X Y : Comp} (f : X ⟶ Y ⨿ X) :
    iterate (whiskerLeft Z f ≫ (leftCoproductComparisonIso Z Y X).inv) = whiskerLeft Z (iterate f) := by
  rw [leftCoproductComparisonIso_inv]
  exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Strength.whiskerLeft_iterate Z f

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
