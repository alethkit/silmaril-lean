module

public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Values
public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Binders
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms

/-! # Normalization of written terms at the original effect bound -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization (Value)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall
  (SumSignature treeSource endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Proofs

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  {e : ε} {A : Ty α}

private theorem subst_lift_beta (b v : Expr (Φ ⊕ Ψ)) (σ : Nat → Expr (Φ ⊕ Ψ)) :
    (b.subst (Expr.liftSubst σ)).subst v.subst0 = b.subst (cons v σ) := by
  change (b.subst (Expr.liftSubst σ)).subst (cons v Expr.var) = _
  simp only [subst_lift_cons, Expr.subst_var]

private theorem normalize_subst {Δ : EffectCtx (Ty α) ε} {a : Expr (Φ ⊕ Ψ)}
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Δ a A e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∀ {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}, Γ.Pure →
      (∀ i, (Γ.get i).1 = .base (slots i)) →
      ∀ {σ : Nat → Expr (Φ ⊕ Ψ)}, NormalEnv S slots Δ σ →
      Normalizes S T Γ slots A e (a.subst σ) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  induction ha with
  | var i _ =>
    intro Γ ss hΓ hs σ hσ
    obtain ⟨v, hv, he⟩ := hσ i
    rw [Expr.subst, he]
    exact normal_value S T hΓ hs v hv
  | unit =>
    intro Γ ss hΓ hs σ hσ
    exact normal_value S T hΓ hs .unit trivial
  | @op Δ f a e hf ha ih =>
    intro Γ ss hΓ hs σ hσ
    have ht := ha.subst_typed (NormalEnv.typed S T hσ hΓ hs)
    have hb : Wf ((instrSrc f, ⊥) :: Γ) (.op f (.var 0)) (instrTrg f) e := .op hf (.var 0 bot_le)
    apply Normalizes.of_eqv S T (CallByValue.op_bind hf ht)
    apply bind S T hΓ hs (ih hΓ hs hσ) hb
    intro Λ target hΛ htarget θ hθ ξ hξ v hv
    cases f with
    | inl f => exact normal_atom S T hΛ htarget f hf v hv
    | inr g => exact normal_sum S T hΛ htarget g hf v hv
  | @let₁ Δ a b A B e ha hb iha ihb =>
    intro Γ ss hΓ hs σ hσ
    have hb' := hb.subst_typed (typed_lift S T (NormalEnv.typed S T hσ hΓ hs) (A, ⊥))
    apply bind S T hΓ hs (iha hΓ hs hσ) hb'
    intro Λ target hΛ htarget θ hθ ξ hξ v hv
    rw [subst_lift_cons]
    exact ihb hΛ htarget (NormalEnv.cons S (NormalEnv.subst S hσ θ hθ ξ hξ) v hv)
  | @pair Δ a b A B e ha hb iha ihb =>
    intro Γ ss hΓ hs σ hσ
    have hsub := NormalEnv.typed S T hσ hΓ hs
    have ha' := ha.subst_typed hsub
    have hb' := hb.subst_typed hsub
    have hpair : Wf ((B, ⊥) :: (A, ⊥) :: Γ) (.pair (.var 1) (.var 0) : Expr (Φ ⊕ Ψ))
        (.product A B) e := .pair (.var 1 bot_le) (.var 0 bot_le)
    apply Normalizes.of_eqv S T (CallByValue.pair_bind ha' hb')
    apply bind S T hΓ hs (iha hΓ hs hσ) (.let₁ (CallByValue.wf_wk0 hb' (A, ⊥)) hpair)
    intro Λ target hΛ htarget θ hθ ξ hξ v hv
    change Normalizes S T Λ target (.product A B) e
      (.let₁ (((b.subst σ).wk0).subst (cons (valueSource S v) ξ))
        (.pair ((valueSource S v).wk0) (.var 0)))
    rw [subst_wk0_cons, Expr.subst_comp]
    have hleft := CallByValue.wf_wk0 ((value_wf S T hΛ htarget v hv).weakenEffect (bot_le : ⊥ ≤ e)) (B, ⊥)
    apply bind S T hΛ htarget (ihb hΛ htarget (NormalEnv.subst S hσ θ hθ ξ hξ))
      (.pair hleft (.var 0 bot_le))
    intro Ξ final hΞ hfinal θ' hθ' ξ' hξ' w hw
    change Normalizes S T Ξ final (.product A B) e
      (.pair ((valueSource S v).wk0.subst (cons (valueSource S w) ξ')) (valueSource S w))
    rw [subst_wk0_cons]
    obtain ⟨v', hv', he⟩ := value_subst S v hv θ' hθ' ξ' hξ'
    rw [he]
    exact normal_value S T hΞ hfinal (.pair v' w) ⟨hv', hw⟩
  | @let₂ Δ a b A B C e ha hb iha ihb =>
    intro Γ ss hΓ hs σ hσ
    have hsub := NormalEnv.typed S T hσ hΓ hs
    have hb' := hb.subst_typed (typed_lift S T (typed_lift S T hsub (A, ⊥)) (B, ⊥))
    apply Normalizes.of_eqv S T (let2_bind S T (ha.subst_typed hsub) hb')
    apply bind S T hΓ hs (iha hΓ hs hσ) (.let₂ (.var 0 bot_le) (wf_wk2 S T (.product A B) hb'))
    intro Λ target hΛ htarget θ hθ ξ hξ v hv
    change Normalizes S T Λ target C e
      (.let₂ (valueSource S v)
        ((b.subst (Expr.liftSubst (Expr.liftSubst σ))).wk2.subst
          (Expr.liftSubst (Expr.liftSubst (cons (valueSource S v) ξ)))))
    rw [subst_wk2_lift_cons, subst_lift2_comp]
    cases v with
    | pair p q =>
      let henv := NormalEnv.subst S hσ θ hθ ξ hξ
      have ht := NormalEnv.typed S T henv hΛ htarget
      have hbody := hb.subst_typed (typed_lift S T (typed_lift S T (Γ := Λ) (ξ := fun i => (σ i).subst ξ) ht (A, ⊥)) (B, ⊥))
      have he := let2_pure_beta S T (value_wf S T hΛ htarget p hv.1) (value_wf S T hΛ htarget q hv.2) hbody
      rw [subst_pair_beta] at he
      exact Normalizes.of_eqv S T he (ihb hΛ htarget
        (NormalEnv.cons S (NormalEnv.cons S henv p hv.1) q hv.2))
  | @inl Δ a A B e ha ih =>
    intro Γ ss hΓ hs σ hσ
    apply Normalizes.of_eqv S T (inl_bind S T (B := B) (ha.subst_typed (NormalEnv.typed S T hσ hΓ hs)))
    apply bind S T hΓ hs (ih hΓ hs hσ) (.inl (.var 0 bot_le))
    intro Λ target hΛ htarget θ hθ ξ hξ v hv
    exact normal_value S T hΛ htarget (.inl v) hv
  | @inr Δ b A B e hb ih =>
    intro Γ ss hΓ hs σ hσ
    apply Normalizes.of_eqv S T (inr_bind S T (A := A) (hb.subst_typed (NormalEnv.typed S T hσ hΓ hs)))
    apply bind S T hΓ hs (ih hΓ hs hσ) (.inr (.var 0 bot_le))
    intro Λ target hΛ htarget θ hθ ξ hξ v hv
    exact normal_value S T hΛ htarget (.inr v) hv
  | @case Δ a l r A B C e ha hl hr iha ihl ihr =>
    intro Γ ss hΓ hs σ hσ
    have hsub := NormalEnv.typed S T hσ hΓ hs
    have hl' := hl.subst_typed (typed_lift S T hsub (A, ⊥))
    have hr' := hr.subst_typed (typed_lift S T hsub (B, ⊥))
    have hcase := case_bind S T (ha.subst_typed hsub) hl' hr'
    apply Normalizes.of_eqv S T hcase
    apply bind S T hΓ hs (iha hΓ hs hσ)
      (.case (.var 0 bot_le) (wf_wk1 S T (.coprod A B) hl') (wf_wk1 S T (.coprod A B) hr'))
    intro Λ target hΛ htarget θ hθ ξ hξ v hv
    change Normalizes S T Λ target C e (.case (valueSource S v)
      ((l.subst (Expr.liftSubst σ)).wk1.subst (Expr.liftSubst (cons (valueSource S v) ξ)))
      ((r.subst (Expr.liftSubst σ)).wk1.subst (Expr.liftSubst (cons (valueSource S v) ξ))))
    simp only [subst_wk1_lift_cons, subst_lift_comp]
    let henv := NormalEnv.subst S hσ θ hθ ξ hξ
    have ht := NormalEnv.typed S T henv hΛ htarget
    have hL := hl.subst_typed (typed_lift S T (Γ := Λ) (ξ := fun i => (σ i).subst ξ) ht (A, ⊥))
    have hR := hr.subst_typed (typed_lift S T (Γ := Λ) (ξ := fun i => (σ i).subst ξ) ht (B, ⊥))
    cases v with
    | inl p =>
      have hp := value_wf S T hΛ htarget p hv
      have hp' := hp.weakenEffect (bot_le : ⊥ ≤ e)
      have he := Eqv.step (Step.reduce (.case (B := B) (.inl hp') hL hR)
        (.let₁ hp' hL) (.case_inl _ _ _))
      have hβ := Eqv.step (Step.let1_beta hp hL)
      rw [subst_lift_beta] at hβ
      exact Normalizes.of_eqv S T (he.trans hβ) (ihl hΛ htarget (NormalEnv.cons S henv p hv))
    | inr p =>
      have hp := value_wf S T hΛ htarget p hv
      have hp' := hp.weakenEffect (bot_le : ⊥ ≤ e)
      have he := Eqv.step (Step.reduce (.case (A := A) (.inr hp') hL hR)
        (.let₁ hp' hR) (.case_inr _ _ _))
      have hβ := Eqv.step (Step.let1_beta hp hR)
      rw [subst_lift_beta] at hβ
      exact Normalizes.of_eqv S T (he.trans hβ) (ihr hΛ htarget (NormalEnv.cons S henv p hv))
  | abort _ ih =>
    intro Γ ss hΓ hs σ hσ
    obtain ⟨p, _, _⟩ := ih hΓ hs hσ
    exact (no_empty_code S T p).elim

variable {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α}

public theorem normalize {a : Expr (Φ ⊕ Ψ)} (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (ss i)) (e : ε)
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a A e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∃ p : Code S T A ss, p.WellTyped S T e ∧ Eqv Γ A e a p.source := by
  obtain ⟨p, hp, he⟩ := normalize_subst S T ha hΓ hs (NormalEnv.identity S hs)
  rw [Expr.subst_var] at he
  exact ⟨p, hp, he⟩

private theorem toMixed_typed {n : Nat} {ss : Fin n → α} {c : α} (p : Code S T (.base c) ss)
    (hp : p.WellTyped S T e) : p.toMixed.WellTyped S T e := by
  induction p with
  | ret v => cases v; exact hp
  | atom f args next ih => exact ⟨hp.1, hp.2.1, hp.2.2.1, ih hp.2.2.2⟩
  | sum g args left right ihl ihr => exact ⟨hp.1, hp.2.1, ihl hp.2.2.1, ihr hp.2.2.2⟩

private theorem toMixed_source {n : Nat} {ss : Fin n → α} {c : α} (p : Code S T (.base c) ss) :
    p.toMixed.source = p.source := by
  induction p with
  | ret v => cases v; rfl
  | atom f args next ih => simp only [Code.toMixed, Program.source, Code.source, ih]
  | sum g args left right ihl ihr => simp only [Code.toMixed, Program.source, Code.source, ihl, ihr]

public theorem normalize_atomic {a : Expr (Φ ⊕ Ψ)} {c : α} (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (ss i)) (e : ε)
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a (.base c) e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∃ p : Mixed.Program S T c ss, p.WellTyped S T e ∧ Eqv Γ (.base c) e a p.source := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  obtain ⟨p, hp, he⟩ := normalize S T hΓ hs e ha
  exact ⟨p.toMixed, toMixed_typed S T p hp, (toMixed_source S T p).symm ▸ he⟩

variable [EffectIteration ε] [DecidableEq α]

public theorem endpoint_reflection {a b : Expr (Φ ⊕ Ψ)} {c : α}
    (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g) (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (ss i)) (e : ε)
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a (.base c) e)
    (hb : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ b (.base c) e)
    {t s : Tm Empty (Φ ⊕ Ψ) Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hu : b.toLetIter Γ.length = some s) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base c) ↔ Eqv Γ (.base c) e a b := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  refine ⟨fun hn => ?_, fun he => he.toLetIter ht hu⟩
  obtain ⟨p, hp, hpa⟩ := normalize_atomic S T hΓ hs e ha
  obtain ⟨q, hq, hqb⟩ := normalize_atomic S T hΓ hs e hb
  have hnp := hpa.toLetIter ht (Mixed.lowers S T p)
  have hnq := hqb.toLetIter hu (Mixed.lowers S T q)
  have he := (Mixed.endpoint_reflection S T visible hΓ hs e p q hp hq).mp
    (hnp.symm.trans (hn.trans hnq))
  exact hpa.trans (he.trans hqb.symm)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Proofs
