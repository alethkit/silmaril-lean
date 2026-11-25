module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.VariableActs
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.ProductBindingActs
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Typing

/-! # Reification of the native sequential categorical interpretation

Interpreting a term in the actual syntactic model and feeding it the packed
context recovers that term by the native equations. The proof is structural on
the quantitative typing derivation; model objects acquire no generation axiom.
-/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless Denotation

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {R : Relation τ Φ}

/-- Native sequential interpretation acts as the source term on its packed
context. The default-annotation invariant is inherited by every subderivation. -/
theorem denoteSeq_acts (hR : R.RenamingClosed) {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (d : HasType .seq Γ e t A) (hΓ : Γ.DefaultAnnotations) :
    Acts Γ (packTerm Γ) (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) d) t := by
  revert hΓ
  induction d with
  | @var n Γ e i hi =>
    intro hΓ
    exact variable_acts hR hΓ i hi
  | @op n Γ e f a hf ha ih =>
    intro hΓ
    have h₀ := ih hΓ
    have h₁ := Acts.of_equates (r := instructionArrow f) (action_instruction (R := R) f ha.top)
    exact h₀.compose hR (packDeriv Γ (⊤ : ε)) h₁
  | @let₁ n Γ Γl Γr e a b A B s ha hb iha ihb =>
    intro hΓ
    have hl := hΓ.split_left s
    have hr := hΓ.split_right s
    have h₀ := split_acts (F := .seq) (R := R) (ε := ε) hR s hΓ
    have h₁ := (iha hr).left hR s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊤ : ε))
    have h₂ := Acts.bind_pack s ha.top (ihb (hl.snoc A (.inr rfl)))
    have hh := h₁.compose hR (HasType.pair s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊤ : ε))) h₂
    have hall := h₀.compose hR (packDeriv Γ (⊤ : ε)) hh
    change Acts Γ (packTerm Γ)
      ((seqData (ε := ε) (F := .seq) (R := R) hR).compose (split (seqData (ε := ε) (F := .seq) (R := R) hR) s)
        ((seqData (ε := ε) (F := .seq) (R := R) hR).compose ((seqData (ε := ε) (F := .seq) (R := R) hR).left (packed Γl) (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) ha))
          (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) hb))) (.let₁ a b)
    rw [seqData_left (ε := ε) (F := .seq) (R := R) hR (packed Γl)
      (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) ha)]
    exact hall
  | @unit n Γ e hd =>
    intro hΓ
    exact discard_acts hR hΓ hd
  | @pair n Γ Γl Γr e a b A B s ha hb iha ihb =>
    intro hΓ
    have hl := hΓ.split_left s
    have hr := hΓ.split_right s
    have h₀ := split_acts (F := .seq) (R := R) (ε := ε) hR s hΓ
    have h₁ := (iha hl).tensor hR s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊥ : ε))
      (packed_quantity_eq hr).le (ihb hr)
    have hall := h₀.compose hR (packDeriv Γ (⊤ : ε)) h₁
    change Acts Γ (packTerm Γ)
      ((seqData (ε := ε) (F := .seq) (R := R) hR).compose (split (seqData (ε := ε) (F := .seq) (R := R) hR) s)
        ((seqData (ε := ε) (F := .seq) (R := R) hR).tensor (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) ha) (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) hb))) (.pair a b)
    simp only [SeqData.tensor]
    rw [seqData_right (ε := ε) (F := .seq) (R := R) hR
      (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) ha) (packed Γr),
      seqData_left (ε := ε) (F := .seq) (R := R) hR A
      (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) hb)]
    exact hall
  | @let₂ n Γ Γl Γr e a b A B C s ha hb iha ihb =>
    intro hΓ
    have hl := hΓ.split_left s
    have hr := hΓ.split_right s
    have h₀ := split_acts (F := .seq) (R := R) (ε := ε) hR s hΓ
    have h₁ := (iha hr).left hR s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊤ : ε))
    have h₂ := Acts.bind₂_pack hR s hl ha.top (ihb ((hl.snoc A (.inr rfl)).snoc B (.inr rfl)))
    have hh := h₁.compose hR (HasType.pair s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊤ : ε))) h₂
    have hall := h₀.compose hR (packDeriv Γ (⊤ : ε)) hh
    change Acts Γ (packTerm Γ)
      ((seqData (ε := ε) (F := .seq) (R := R) hR).compose (split (seqData (ε := ε) (F := .seq) (R := R) hR) s)
        ((seqData (ε := ε) (F := .seq) (R := R) hR).compose ((seqData (ε := ε) (F := .seq) (R := R) hR).left (packed Γl) (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) ha))
          ((seqData (ε := ε) (F := .seq) (R := R) hR).compose ((seqData (ε := ε) (F := .seq) (R := R) hR).associatorInv (packed Γl) A B)
            (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) hb)))) (.let₂ a b)
    rw [seqData_left (ε := ε) (F := .seq) (R := R) hR (packed Γl)
      (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) ha),
      seqData_associatorInv (ε := ε) (F := .seq) (R := R) hR]
    exact hall
  | inl cap => exact False.elim cap
  | inr cap => exact False.elim cap
  | case cap => exact False.elim cap
  | abort cap => exact False.elim cap
  | iter cap => exact False.elim cap

/-- Feeding the singleton packing map to native interpretation recovers the
original quotient arrow. -/
theorem denoteSeq_reify (hR : R.RenamingClosed) {A B : τ} {e : ε} {t : Term Φ 1}
    (d : HasType .seq (input A) e t B) :
    compose (ε := ε) (F := .seq) (R := R) hR (leftUnitInv A)
      (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) d) =
      ofArrow (R := R) ⟨t, ⟨d.top⟩⟩ := by
  obtain ⟨r, hr, he⟩ := denoteSeq_acts (R := R) hR d (input_default A)
  rw [← hr]
  apply Quotient.sound
  change Equates (ε := ε) .seq R (input A)
    (composeArrow (leftUnitInvArrow A) r).val t B
  simpa only [composeArrow, composeTerm, leftUnitInvArrow, continuation_atIndex,
    input, packTerm_snoc_used, packTerm_nil, Tm.lift, Tm.rename, action] using he

/-- The interpretation itself is the original quotient arrow preceded by the
unitor that removes the packed empty-context unit. -/
theorem denoteSeq_arrow (hR : R.RenamingClosed) {A B : τ} {e : ε} {t : Term Φ 1}
    (d : HasType .seq (input A) e t B) :
    denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) d =
      compose (ε := ε) (F := .seq) (R := R) hR (leftUnit A) (ofArrow (R := R) ⟨t, ⟨d.top⟩⟩) := by
  have h := congrArg (compose (ε := ε) (F := .seq) (R := R) hR (leftUnit A)) (denoteSeq_reify (R := R) hR d)
  rw [← compose_assoc (ε := ε) (F := .seq) (R := R) hR
      (leftUnit A) (leftUnitInv A)
      (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) d),
    leftUnit_leftUnitInv (ε := ε) (F := .seq) (R := R) hR A] at h
  exact (identity_compose (ε := ε) (F := .seq) (R := R) hR
    (denoteSeq (seqModel (ε := ε) (F := .seq) (R := R) hR) d)).symm.trans h

end Silmaril.Isotope.Refinement.Models.Syntactic
