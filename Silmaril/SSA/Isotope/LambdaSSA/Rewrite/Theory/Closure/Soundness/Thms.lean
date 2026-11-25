module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Outward.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ClosureSoundness

/-! # Categorical soundness of the substitution-closed native λSSA equations -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Substituting an argument with a pure denotation composes the body's
categorical denotation with the corresponding environment extension. -/
theorem Semantics.Categorical.RegionDenotes.substValue
    {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {a : Tm Φ} {A : τ}
    {hr : Region.HasType (A :: Γ) r L}
    {f : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hr f) {p : ctxObj M Γ ⟶ M.obj A} {ha : Tm.HasType Γ a A}
    (da : Denotes J M ha (J.map p)) :
    ∃ ht : Region.HasType Γ (r.substVars (Tm.singleSubst a)) L,
      RegionDenotes J M ht (J.map (CartesianMonoidalCategory.lift (𝟙 _) p) ≫ f) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.regionDenotes_substValue_proof J M d da

variable [RegionTypingCoherent (Φ := Φ) J M]

/-- Constructor-value let β holds for any typed subject, including nested CFGs. -/
theorem Semantics.Categorical.denoteRegion_letValue
    {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {a : Tm Φ} {A : τ}
    (ha : Tm.BranchValue Γ a A) (hr : Region.HasType (A :: Γ) r L)
    (ht : Region.HasType Γ (r.substVars (Tm.singleSubst a)) L) :
    denoteRegion J M (.let₁ ha.hasType hr) = denoteRegion J M ht := by
  obtain ⟨_, _, ds, dt⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.letValue_common J M ha hr
  exact (RegionDenotes.eq_denote J M ds).symm.trans (RegionDenotes.eq_denote (h := ht) J M dt)

/-- The substitution-closed native region equations preserve the chosen
categorical denotation. Outward CFG elimination uses a central unit comparison. -/
theorem Region.SubstitutionEquiv.sound
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Region.SubstitutionEquiv Γ r s L)
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  obtain ⟨_, _, _, dr, ds⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.substitutionEquiv_common J M hu h
  exact (RegionDenotes.eq_denote (h := hr) J M dr).symm.trans
    (RegionDenotes.eq_denote (h := hs) J M ds)

/-- Native equivalent regions remain denotationally equal after substituting
any well-typed continuation family on both sides. -/
theorem Region.SubstitutionEquiv.sound_lsubst
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ} (h : Region.SubstitutionEquiv Γ r s L)
    {σ : Nat → Region Φ} (hσ : Region.LSubst.HasType Γ L K σ)
    (hr : Region.HasType Γ (r.lsubst σ) K) (hs : Region.HasType Γ (s.lsubst σ) K) :
    denoteRegion J M hr = denoteRegion J M hs :=
  (h.lsubst hσ).sound J M hu hr hs

end Silmaril.Isotope.LambdaSSA
