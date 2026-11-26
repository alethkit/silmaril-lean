module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.IdentityLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Let.Identity.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IdentityLet

/-! # Soundness of the guarded identity-let extension -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.IdentityLet

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Semantics.Categorical
open Paper.TypeCategory (denoteArrow ofType)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IdentityLet (stepDenotes eqvSound arrowSound)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

/-- The two guarded regions have a common structural arrow. Their bound
expressions and continuations retain their exact typing. -/
theorem Step.denotes (hu : IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (e : Step Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f :=
  stepDenotes J M hu e hr hs

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

variable (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
  Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

include shared in
/-- Every typed contextual derivation in the optional extension preserves the
chosen denotation in the coherent shared-tensor Paper model. -/
theorem Eqv.sound {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (e : Eqv Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) : denoteRegion J M hr = denoteRegion J M hs :=
  eqvSound J M shared e hr hs

include shared in
/-- The singleton denotation descends on homs along the optional projection. -/
theorem denoteArrow_eq_of_projection_eq {A B : τ} (f g : ofType (Φ := Φ) A ⟶ ofType B)
    (h : projection.map f = projection.map g) : denoteArrow J M f = denoteArrow J M g :=
  arrowSound J M shared f g h

end Silmaril.Isotope.LambdaSSA.Region.Paper.IdentityLet
