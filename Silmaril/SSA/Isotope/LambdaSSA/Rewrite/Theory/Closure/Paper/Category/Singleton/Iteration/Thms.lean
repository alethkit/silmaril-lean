module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonIteration

/-! # Iteration laws for the chosen singleton coproducts of the paper quotient -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B C : τ}

/-- Feedback on a region returning an exact sum is represented by a one-label CFG. -/
theorem iterateSum_ofRegion {p : Region Φ} (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    iterateSum (ofRegion hp) = ofRegion (SyntacticCategory.iterateRegion_valueBranches hp) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonIteration.iterateSum_ofRegion hp

/-- The categorical copair on guarded representatives is case analysis on the exact sum. -/
theorem coprod_desc_ofRegion {p q : Region Φ} (hp : ValueBranches [A] p [C])
    (hq : ValueBranches [B] q [C]) :
    (sumIso A B).hom ≫ coprod.desc (ofRegion hp) (ofRegion hq) =
      ofRegion (CfgEta.TypeCategory.caseValueBranches hp hq) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonIteration.coprod_desc_ofRegion hp hq

/-- Unfold the one-label feedback CFG by one step. -/
theorem iterate_fixpoint {X Y : TypeCategory (τ := τ) Φ} (f : X ⟶ Y ⨿ X) :
    iterate f = f ≫ coprod.desc (𝟙 Y) (iterate f) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonIteration.iterate_fixpoint f

/-- Postcomposition maps the outward results of a feedback step. -/
theorem iterate_naturality {X Y Z : TypeCategory (τ := τ) Φ} (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z) :
    iterate f ≫ g = iterate (f ≫ coprod.map g (𝟙 X)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonIteration.iterate_naturality f g

/-- Two feedback cuts identify the two local labels of the same state type. -/
theorem iterate_codiagonal {X Y : TypeCategory (τ := τ) Φ} (f : X ⟶ (Y ⨿ X) ⨿ X) :
    iterate (iterate f) = iterate (f ≫ coprod.desc (𝟙 (Y ⨿ X)) coprod.inr) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonIteration.iterate_codiagonal f

/-- A commuting square for a constructor-valued state change is uniform under iteration. -/
theorem iterate_uniformity_ofBranchValue {A D B : τ} {a : Tm Φ} (ha : Tm.BranchValue [A] a D)
    (f : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A)
    (g : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType D)
    (comm : f ≫ coprod.map (𝟙 (ofType B)) (ofRegion (r := .br 0 a) (.br (ℓ := 0) rfl ha)) =
      ofRegion (r := .br 0 a) (.br (ℓ := 0) rfl ha) ≫ g) :
    iterate f = ofRegion (r := .br 0 a) (.br (ℓ := 0) rfl ha) ≫ iterate g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonIteration.iterate_uniformity_ofBranchValue ha f g comm

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
