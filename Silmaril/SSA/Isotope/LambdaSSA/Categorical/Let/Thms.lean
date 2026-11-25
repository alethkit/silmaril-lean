module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms

/-! # Denotational congruence for LambdaSSA let scrutinees -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Changing just the scrutinee of a typed region let preserves its graph
arrow whenever the scrutinees have a common computation arrow. -/
theorem RegionDenotes.let₁_scrutinee_congr {Γ : VCtx τ} {A : τ} {L : LCtx τ}
    {a b : Tm Φ} {r : Region Φ} {ha : Tm.HasType Γ a A} {hb : Tm.HasType Γ b A}
    {hr : Region.HasType (A :: Γ) r L} {p : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    {f : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (labelObj M L)}
    (da : Denotes J M ha p) (db : Denotes J M hb p) (dr : RegionDenotes J M hr f) :
    RegionDenotes J M (.let₁ ha hr) (bind J p f) ∧
      RegionDenotes J M (.let₁ hb hr) (bind J p f) :=
  ⟨.let₁ da dr, .let₁ db dr⟩

/-- The fixed-body scrutinee rule for chosen denotations in a
region-coherent model. -/
theorem denoteRegion_let₁_scrutinee_congr [RegionTypingCoherent (Φ := Φ) J M]
    {Γ : VCtx τ} {A : τ} {L : LCtx τ} {a b : Tm Φ} {r : Region Φ}
    {ha : Tm.HasType Γ a A} {hb : Tm.HasType Γ b A} (hr : Region.HasType (A :: Γ) r L)
    (h : denote J M ha = denote J M hb) :
    denoteRegion J M (.let₁ ha hr) = denoteRegion J M (.let₁ hb hr) := by
  obtain ⟨dl, dr⟩ := RegionDenotes.let₁_scrutinee_congr J M
    (denote_spec J M ha) (h.symm ▸ denote_spec J M hb) (denoteRegion_spec J M hr)
  exact (dl.eq_denote J M).symm.trans (dr.eq_denote J M)

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
