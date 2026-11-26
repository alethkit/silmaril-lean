module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms

/-! # Soundness of the combined singleton extension -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedDenotation

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.WithProjectionReturnsAndUnitEta

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem step_denotes {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (step : Step Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  rcases step with h | h
  · exact ⟨_, denoteRegion_spec J M hr, (h.sound J M hr hs).symm ▸ denoteRegion_spec J M hs⟩
  · exact h.denotes J M hr hs

variable (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
  Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
include shared

theorem eqv_sound {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (equiv : Paper.Extension.Eqv Step Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Paper.Extension.Eqv.sound J M shared (fun h hr hs => step_denotes J M h hr hs) equiv hr hs

set_option backward.isDefEq.respectTransparency false in
theorem baseDenote_respects_projection {A B : τ}
    {f g : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType B}
    (same : (projection (τ := τ) (Φ := Φ)).map f = (projection (τ := τ) (Φ := Φ)).map g) :
    Paper.TypeCategory.denoteArrow J M f = Paper.TypeCategory.denoteArrow J M g := by
  obtain ⟨_, hf, rfl⟩ := Paper.TypeCategory.exists_ofRegion f
  obtain ⟨_, hg, rfl⟩ := Paper.TypeCategory.exists_ofRegion g
  have e := (Paper.Extension.Singleton.ofRegion_eq_iff Step hf hg).1 same
  rw [Paper.TypeCategory.denoteArrow_ofRegion J M shared, Paper.TypeCategory.denoteArrow_ofRegion J M shared]
  unfold denoteSingletonRegion
  rw [eqv_sound J M shared e]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedDenotation
