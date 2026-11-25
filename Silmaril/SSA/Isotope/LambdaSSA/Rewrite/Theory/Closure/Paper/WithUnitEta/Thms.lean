module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithUnitEta

/-! # Sound guarded unit η and its singleton quotient equation -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithUnitEta

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- Typed substitution and renaming give unit η at every constructor-valued unit branch. -/
theorem branch_unit_eta {a : Tm Φ} {ℓ : Nat}
    (ha : Tm.BranchValue Γ a Silmaril.unit) (hℓ : At L ℓ (Silmaril.unit : τ)) :
    Eqv Γ (.br ℓ .unit) (.br ℓ a) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithUnitEta.branch_unit_eta ha hℓ

/-- The literal unit return at unit is the identity in the opt-in singleton quotient. -/
theorem map_discard_eq_id :
    (projection (τ := τ) (Φ := Φ)).map
      (Paper.TypeCategory.discardArrow (Φ := Φ) (Silmaril.unit : τ)) =
      𝟙 ((projection (τ := τ) (Φ := Φ)).obj (Paper.TypeCategory.ofType Silmaril.unit)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithUnitEta.map_discard_eq_id

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Seed soundness uses terminality of the interpreted unit in the value category. -/
theorem Step.denotes (e : Step Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithUnitEta.step_denotes J M e hr hs

/-- The guarded extension is sound under the existing Paper model assumptions. -/
theorem Eqv.sound [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    (e : Eqv Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Extension.Eqv.sound J M shared (fun h => h.denotes J M) e hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithUnitEta
