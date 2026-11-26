module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedDenotation

/-! # Arbitrary-model soundness for the projection-return and unit-η join -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The first and second projection-return rules use binary-let return fusion and
constructor β. Guarded unit η uses terminality of the interpreted value unit. -/
theorem step_denotes {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (step : Step Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedDenotation.step_denotes J M step hr hs

variable (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
  Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
include shared

/-- The joined contextual closure preserves chosen region denotations under
the ordinary Paper model hypotheses. -/
theorem eqv_sound {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (equiv : Paper.Extension.Eqv Step Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedDenotation.eqv_sound J M shared equiv hr hs

/-- Ordinary singleton denotation respects equality after projecting to the
join. This is the respectfulness proof for the descended map on each hom. -/
theorem baseDenote_respects_projection {A B : τ}
    {f g : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType B}
    (same : (projection (τ := τ) (Φ := Φ)).map f = (projection (τ := τ) (Φ := Φ)).map g) :
    Paper.TypeCategory.denoteArrow J M f = Paper.TypeCategory.denoteArrow J M g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedDenotation.baseDenote_respects_projection
    J M shared same

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta
