module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ContextMerge
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.TypeMapVariables
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.Renaming
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Structural

/-! # Common semantic typings for covariant type comparisons

The witness is an actual quantitative typing of the same raw term. Its two
commuting diagrams compare independent hidden type choices without assuming
that those types are equal.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {α : Type u} [DecidableEq α] [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} (Ty α) Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F)

omit [DecidableEq α] in
/-- Equality transport of the raw term does not alter the interpreted arrow. -/
theorem denote_term_transport {n : Nat} {Γ : QCtx (Ty α) n} {e : ε} {t t' : Term Φ n} {A : Ty α}
    (h : HasType F Γ e t A) (ht : t = t') :
    denote M.toSeqData K (ht ▸ h) = denote M.toSeqData K h := by
  cases ht
  rfl

/-- A common typing, together with its two pure comparison squares. -/
def TypingComparison {n : Nat} {Γ Δ : QCtx (Ty α) n} {e e' : ε} {t : Term Φ n} {A B : Ty α}
    (h : HasType F Γ e t A) (k : HasType F Δ e' t B) (hc : QCtx.Aligned Γ Δ) : Prop :=
  ∃ l : HasType F (QCtx.merge Γ Δ) (⊤ : ε) t (mergeType A B),
    M.compose (denote M.toSeqData K h) (mergeLeft M A B) =
      M.compose (mergeContext M Γ Δ hc).1.1 (denote M.toSeqData K l) ∧
    M.compose (denote M.toSeqData K k) (mergeRight M A B) =
      M.compose (mergeContext M Γ Δ hc).2.1 (denote M.toSeqData K l)

/-- The variable comparison is the naturality square for its selected context slot. -/
theorem TypingComparison.var {n : Nat} {Γ Δ : QCtx (Ty α) n} {e e' : ε} (i : Fin n)
    (h : Γ.VarAllowed i) (k : Δ.VarAllowed i) (hc : QCtx.Aligned Γ Δ) :
    TypingComparison M K (.var (e := e) i h) (.var (e := e') i k) hc := by
  refine ⟨.var i (h.merge k), ?_, ?_⟩
  · change M.compose («variable» M.toSeqData i h) (mergeArrows M (Γ i).1 (Δ i).1).1.1 =
      M.compose (mergeContext M Γ Δ hc).1.1 («variable» M.toSeqData i (h.merge k))
    rw [mergeContext_eq_contextTypeMap]
    exact (congrArg Subtype.val (contextTypeMap_variable M.toSeqData Γ (QCtx.merge Γ Δ)
      (fun j => (mergeArrows M (Γ j).1 (Δ j).1).1)
      (fun j => Usage.merge_zero_left _ _ (hc j)) i h (h.merge k))).symm
  · change M.compose («variable» M.toSeqData i k) (mergeArrows M (Γ i).1 (Δ i).1).2.1 =
      M.compose (mergeContext M Γ Δ hc).2.1 («variable» M.toSeqData i (h.merge k))
    rw [mergeContext_eq_contextTypeMap]
    exact (congrArg Subtype.val (contextTypeMap_variable M.toSeqData Δ (QCtx.merge Γ Δ)
      (fun j => (mergeArrows M (Γ j).1 (Δ j).1).2)
      (fun j => Usage.merge_zero_right _ _ (hc j)) i k (h.merge k))).symm

/-- The common unit derivation uses the actual discardability of both contexts. -/
theorem TypingComparison.unit {n : Nat} {Γ Δ : QCtx (Ty α) n} {e e' : ε}
    (h : Γ.Discardable) (k : Δ.Discardable) (hc : QCtx.Aligned Γ Δ) :
    TypingComparison M K (.unit (e := e) h) (.unit (e := e') k) hc := by
  refine ⟨.unit (h.merge k), ?_, ?_⟩
  · change M.compose (discard M.toSeqData h) (M.identity _) =
      M.compose (mergeContext M Γ Δ hc).1.1 (discard M.toSeqData (h.merge k))
    rw [M.compose_identity]
    exact (M.toSeqData.pure_discard_natural _ (mergeContext M Γ Δ hc).1.2 _ _).symm
  · change M.compose (discard M.toSeqData k) (M.identity _) =
      M.compose (mergeContext M Γ Δ hc).2.1 (discard M.toSeqData (h.merge k))
    rw [M.compose_identity]
    exact (M.toSeqData.pure_discard_natural _ (mergeContext M Γ Δ hc).2.2 _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- A pair of semantic weakening factorizations lifts a common typing. -/
theorem TypingComparison.of_factors (N : ControlEnvironment K)
    {n : Nat} {Γ Γ' Δ Δ' : QCtx (Ty α) n} {e e' η η' : ε} {t : Term Φ n} {A B : Ty α}
    (h : HasType F Γ e t A) (k : HasType F Δ e' t B)
    (h' : HasType F Γ' η t A) (k' : HasType F Δ' η' t B)
    (w : QCtx.Weakening Γ Γ' id) (v : QCtx.Weakening Δ Δ' id)
    (wm : QCtx.Weakening (QCtx.merge Γ Δ) (QCtx.merge Γ' Δ') id)
    (hc : QCtx.Aligned Γ Δ) (hc' : QCtx.Aligned Γ' Δ')
    (eh : denote M.toSeqData K h = M.compose (weaken M.toSeqData w) (denote M.toSeqData K h'))
    (ek : denote M.toSeqData K k = M.compose (weaken M.toSeqData v) (denote M.toSeqData K k'))
    (c : TypingComparison M K h' k' hc') : TypingComparison M K h k hc := by
  obtain ⟨l, hl, hr⟩ := c
  obtain ⟨lr, her⟩ := denote_rename_exists M.toSeqModel K N l id wm
  let l' : HasType F (QCtx.merge Γ Δ) (⊤ : ε) t (mergeType A B) := (Tm.rename_id t) ▸ lr
  have he : denote M.toSeqData K l' = M.compose (weaken M.toSeqData wm) (denote M.toSeqData K l) :=
    (denote_term_transport M K lr (Tm.rename_id t)).trans her
  refine ⟨l', ?_, ?_⟩
  · rw [eh, M.compose_assoc, hl, ← M.compose_assoc, he, ← M.compose_assoc]
    exact congrArg (fun f => M.compose f (denote M.toSeqData K l))
      (congrArg Subtype.val (mergeContext_weaken_fst M w v wm hc hc')).symm
  · rw [ek, M.compose_assoc, hr, ← M.compose_assoc, he, ← M.compose_assoc]
    exact congrArg (fun f => M.compose f (denote M.toSeqData K l))
      (congrArg Subtype.val (mergeContext_weaken_snd M w v wm hc hc')).symm

set_option backward.isDefEq.respectTransparency false in
/-- A comparison on a covering support extends to the original contexts.
Only genuinely discardable omitted slots are restored. -/
theorem TypingComparison.of_restrict (N : ControlEnvironment K)
    {n : Nat} {Γ Δ : QCtx (Ty α) n} {e e' : ε} {t : Term Φ n} {A B : Ty α}
    (h : HasType F Γ e t A) (k : HasType F Δ e' t B) (hc : QCtx.Aligned Γ Δ)
    (p : Fin n → Bool) (hp : Term.Covered p t)
    (hc' : TypingComparison M K (h.restrict p hp) (k.restrict p hp) (hc.restrict p)) :
    TypingComparison M K h k hc := by
  let w := h.coveringWeakening p hp
  let v := k.coveringWeakening p hp
  have dh : ∀ i, p i = false → Usage.zero ≤ QCtx.effective Γ i := by
    intro i hi
    have ht : Term.uses t i = false := by
      cases hh : Term.uses t i
      · rfl
      · exact False.elim (Bool.noConfusion (hi.symm.trans (hp i hh)))
    exact (h.slotAllows i).2 ht
  have dk : ∀ i, p i = false → Usage.zero ≤ QCtx.effective Δ i := by
    intro i hi
    have ht : Term.uses t i = false := by
      cases hh : Term.uses t i
      · rfl
      · exact False.elim (Bool.noConfusion (hi.symm.trans (hp i hh)))
    exact (k.slotAllows i).2 ht
  let wm := QCtx.weakening_merge_restrict Γ Δ p dh dk
  exact TypingComparison.of_factors M K N h k (h.restrict p hp) (k.restrict p hp)
    w v wm hc (hc.restrict p) (denote_restrict M.toSeqModel K N h p hp)
    (denote_restrict M.toSeqModel K N k p hp) hc'

end Silmaril.Isotope.Refinement.Models.Denotation
