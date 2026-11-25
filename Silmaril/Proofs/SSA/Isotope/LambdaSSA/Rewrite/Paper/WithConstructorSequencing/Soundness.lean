module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

/-! # Denotational soundness of the constructor sequencing steps -/

public section

universe u v m n x y

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.UnaryReturn
open Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend duplicate)
open scoped MonoidalCategory

section Typing

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

theorem step_valueBranches (h : Paper.WithConstructorSequencing.Step Γ r s L) : ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases h with
  | pair ha hb =>
    exact ⟨returnOnce_valueBranches (.pair ha.typed.1 hb.typed.1),
      .let₁ ha.typed.1 (.let₁ (hb.typed.1.rename (Ren.wk _ _))
        (.br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))⟩
  | inl ha =>
    exact ⟨returnOnce_valueBranches (.inl ha.typed.1),
      .let₁ ha.typed.1 (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl)))⟩
  | inr ha =>
    exact ⟨returnOnce_valueBranches (.inr ha.typed.1),
      .let₁ ha.typed.1 (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl)))⟩

end Typing

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A B : τ} {t : Tm Φ}
  {L : LCtx τ} {r s : Region Φ}
  {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C] [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

private theorem extend_snd {E X : V} (f : J.obj E ⟶ J.obj X) :
    extend J f ≫ J.map (snd E X) = f := by
  simp only [extend, leftTensor, id_whiskerRight, Category.id_comp, Category.assoc]
  rw [FreydCategory.whiskerLeft_snd J, ← J.map_comp_assoc]
  simp [duplicate]

set_option backward.isDefEq.respectTransparency false in
private theorem denote_inl_sequence (ha : Tm.HasType Γ t A) :
    denoteRegion J M (returnOnce_valueBranches (.inl (B := B) ha)).hasType =
      denoteRegion J M
        (.let₁ ha (.br (ℓ := 0) (L := [Silmaril.coprod A B]) rfl (.inl (.var (i := 0) rfl)))) := by
  let i : At [Silmaril.coprod A B] 0 (Silmaril.coprod A B) := rfl
  have da := denote_spec J M ha
  have dv := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At (A :: Γ) 0 A)
  have original := RegionDenotes.br (h := i) (Denotes.inl da)
  have sequenced := RegionDenotes.let₁ da (RegionDenotes.br (h := i) (Denotes.inl dv))
  have comparison : denoteRegion J M (.br i (.inl (B := B) ha)) = denoteRegion J M
      (returnOnce_valueBranches (.inl (B := B) ha)).hasType :=
    denoteRegion_branchBind J M (FreydCategory.CentralUnit.unit_central (J := J)) i (.inl ha)
  rw [← comparison, ← RegionDenotes.eq_denote J M original, ← RegionDenotes.eq_denote J M sequenced]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, lookup, ctxObj, ← Category.assoc, extend_snd]

set_option backward.isDefEq.respectTransparency false in
private theorem denote_inr_sequence (ha : Tm.HasType Γ t B) :
    denoteRegion J M (returnOnce_valueBranches (.inr (A := A) ha)).hasType =
      denoteRegion J M
        (.let₁ ha (.br (ℓ := 0) (L := [Silmaril.coprod A B]) rfl (.inr (.var (i := 0) rfl)))) := by
  let i : At [Silmaril.coprod A B] 0 (Silmaril.coprod A B) := rfl
  have da := denote_spec J M ha
  have dv := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At (B :: Γ) 0 B)
  have original := RegionDenotes.br (h := i) (Denotes.inr da)
  have sequenced := RegionDenotes.let₁ da (RegionDenotes.br (h := i) (Denotes.inr dv))
  have comparison : denoteRegion J M (.br i (.inr (A := A) ha)) = denoteRegion J M
      (returnOnce_valueBranches (.inr (A := A) ha)).hasType :=
    denoteRegion_branchBind J M (FreydCategory.CentralUnit.unit_central (J := J)) i (.inr ha)
  rw [← comparison, ← RegionDenotes.eq_denote J M original, ← RegionDenotes.eq_denote J M sequenced]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, lookup, ctxObj, ← Category.assoc, extend_snd]

theorem step_sound (e : Paper.WithConstructorSequencing.Step Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  cases e with
  | pair ha hb => exact denote_pair_boundReturn_sequencing J M (i := 0) rfl ha.typed.1 hb.typed.1
  | inl ha => exact denote_inl_sequence J M ha.typed.1
  | inr ha => exact denote_inr_sequence J M ha.typed.1

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing
