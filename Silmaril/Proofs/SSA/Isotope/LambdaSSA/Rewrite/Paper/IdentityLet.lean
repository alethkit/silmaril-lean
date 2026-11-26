module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.IdentityLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Let.Identity.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Let.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms

/-! # Soundness of guarded identity-let contraction -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IdentityLet

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Region Region.Paper.TypeCategory
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

theorem stepDenotes (hu : IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (e : Paper.IdentityLet.Step Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  cases e with
  | let₁ h body =>
    obtain ⟨_, dl, dr⟩ := identityLet_denotes J M hu h
    obtain ⟨_, db⟩ := regionDenotes_exists J M body.hasType
    exact ⟨_, RegionDenotes.let₁_scrutinee_congr J M dl dr db⟩

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

variable (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
  Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

include shared in
theorem eqvSound {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (e : Paper.IdentityLet.Eqv Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) : denoteRegion J M hr = denoteRegion J M hs :=
  Paper.Extension.Eqv.sound J M shared
    (fun h => stepDenotes J M (FreydCategory.CentralUnit.unit_central (J := J)) h) e hr hs

include shared in
theorem arrowSound {A B : τ} (f g : ofType (Φ := Φ) A ⟶ ofType B)
    (h : Paper.IdentityLet.projection.map f = Paper.IdentityLet.projection.map g) :
    denoteArrow J M f = denoteArrow J M g := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion f
  obtain ⟨s, hs, rfl⟩ := exists_ofRegion g
  have eq := (Paper.Extension.Singleton.ofRegion_eq_iff _ hr hs).1 h
  rw [denoteArrow_ofRegion J M shared, denoteArrow_ofRegion J M shared]
  unfold denoteSingletonRegion
  rw [eqvSound J M shared eq hr.hasType hs.hasType]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IdentityLet
