module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ComparisonBinders
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ComparisonCaseSupport

/-! # The common semantic typing induction

The optional iteration step is an admissibility premise used to share this
proof between case and iteration models. It is discharged by their actual
control structure in the public coherence theorems.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [DecidableEq α] [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} (Ty α) Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F)

/-- Every two typings of this raw term admit a common semantic typing. -/
def HasTypingComparison {n : Nat} (a : Term Φ n) : Prop :=
  ∀ {Γ Δ : QCtx (Ty α) n} {e e' : ε} {A B : Ty α}
    (h : HasType F Γ e a A) (k : HasType F Δ e' a B) (hc : QCtx.Aligned Γ Δ),
    TypingComparison M K h k hc

/-- Admissibility of the optional loop step in the shared syntax induction. -/
def IterationComparisonRule : Prop :=
  ∀ {n : Nat} (a : Term Φ n) (b : Term Φ (n+1)),
    HasTypingComparison M K a → HasTypingComparison M K b → HasTypingComparison M K (.iter a b)

variable (it : F.HasIter → ∀ {A B : Ty α}, M.Hom A (coprod B A) → M.Hom A B)
local notation "L" => ControlData.ofCase M F it

/-- Quantitative support normalization and covariant type comparison cover all syntax. -/
theorem hasTypingComparison (N : ControlEnvironment L) (HI : IterationComparisonRule M L)
    {n : Nat} (a : Term Φ n) : HasTypingComparison M L a := by
  induction a with
  | bv i =>
    intro Γ Δ e e' A B h k hc
    cases h with
    | var i h => cases k with | var i k => exact TypingComparison.var M L i h k hc
  | fv x => exact nomatch x
  | op f a ih =>
    intro Γ Δ e e' A B h k hc
    cases h with
    | op hf ha =>
      cases k with
      | op kf ka => exact TypingComparison.op M L f hf kf ha ka hc (ih ha ka hc)
  | unit =>
    intro Γ Δ e e' A B h k hc
    cases h with
    | unit h => cases k with | unit k => exact TypingComparison.unit M L h k hc
  | pair a b iha ihb =>
    intro Γ Δ e e' A B h k hc
    cases h with
    | pair s ha hb =>
      cases k with
      | pair t ka kb =>
        exact TypingComparison.pair_support M L N s t hc ha hb ka kb
          (iha ha.support ka.support (ha.support_aligned ka))
          (ihb hb.support kb.support (hb.support_aligned kb))
  | let₁ a b iha ihb =>
    intro Γ Δ e e' A B h k hc
    cases h with
    | let₁ s ha hb =>
      cases k with
      | let₁ t ka kb =>
        exact TypingComparison.let₁_support M L N s t hc ha hb ka kb
          (iha ha.support ka.support (ha.support_aligned ka))
          (ihb hb.outerSupport₁ kb.outerSupport₁ ((hb.outerSupport₁_aligned kb).snoc _ _))
  | let₂ a b iha ihb =>
    intro Γ Δ e e' A B h k hc
    cases h with
    | let₂ s ha hb =>
      cases k with
      | let₂ t ka kb =>
        exact TypingComparison.let₂_support M L N s t hc ha hb ka kb
          (iha ha.support ka.support (ha.support_aligned ka))
          (ihb hb.outerSupport₂ kb.outerSupport₂ (((hb.outerSupport₂_aligned kb).snoc _ _).snoc _ _))
  | inl a ih =>
    intro Γ Δ e e' A B h k hc
    cases h with
    | inl cap ha =>
      cases k with
      | inl _ ka => exact TypingComparison.inl M it cap ha ka hc (ih ha ka hc)
  | inr a ih =>
    intro Γ Δ e e' A B h k hc
    cases h with
    | inr cap ha =>
      cases k with
      | inr _ ka => exact TypingComparison.inr M it cap ha ka hc (ih ha ka hc)
  | abort a ih =>
    intro Γ Δ e e' A B h k hc
    cases h with
    | abort cap ha =>
      cases k with
      | abort _ ka => exact TypingComparison.abort M it cap ha ka hc (ih ha ka hc)
  | case a l r iha ihl ihr =>
    intro Γ Δ e e' A B h k hc
    cases h with
    | case cap s ha hl hr =>
      cases k with
      | case _ t ka kl kr =>
        exact TypingComparison.case_support M it N cap s t hc ha ka hl kl hr kr
          (iha ha.support ka.support (ha.support_aligned ka))
          (ihl _ _ ((hl.caseOuter_aligned hr kl kr).snoc _ _))
          (ihr _ _ ((hl.caseOuter_aligned hr kl kr).snoc _ _))
  | iter a b iha ihb => exact HI a b iha ihb

/-- Common semantic typing implies ordinary coherence on a fixed judgment. -/
theorem TypingComparison.eq {n : Nat} {Γ : QCtx (Ty α) n} {e e' : ε} {a : Term Φ n} {A : Ty α}
    (h : HasType F Γ e a A) (k : HasType F Γ e' a A)
    (c : TypingComparison M K h k (QCtx.Aligned.refl Γ)) :
    denote M.toSeqData K h = denote M.toSeqData K k := by
  obtain ⟨l, hl, hr⟩ := (TypingComparison.diagonal_iff M K h k (QCtx.Aligned.refl Γ)).mp c
  have he := purePair_components_heq M (congrArg packed (QCtx.merge_self Γ)) (mergeContext_self M Γ)
  have hm : (mergeContext M Γ Γ (QCtx.Aligned.refl Γ)).1 = (mergeContext M Γ Γ (QCtx.Aligned.refl Γ)).2 :=
    eq_of_heq (he.1.trans he.2.symm)
  rw [hl, hr, hm]

end Silmaril.Isotope.Refinement.Models.Denotation
