module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Soundness.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Soundness

/-! # Literal CFG η soundness with shared tensor comparisons

This soundness theorem requires equality-induced tensor comparisons in
addition to the premises of native `SubstitutionEquiv.sound`. Linked CFG
η and linked fixpoint have separate soundness theorems at the native
model boundary.
-/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

/-- Literal one-block CFG η and all its typed outgoing substitution
instances preserve denotation under the explicit shared-tensor premise. -/
theorem Eqv.sound_sharedTensor
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Eqv Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.sound_sharedTensor J M hu shared h hr hs

end Silmaril.Isotope.LambdaSSA.Region.CfgEta
