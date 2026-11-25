module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.FreeTree.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Equations

/-! # Normalization by substituting normal values in typed source expressions -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Proofs

universe u r

variable {α Φ : Type u} (S : Signature α Φ)
variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]

variable {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

theorem value_wf {A : Ty α} (p : Value S slots A) (hp : p.Pure (ε := ε) S)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) :
    letI := S.endpoints
    Wf Γ (p.source S) A (⊥ : ε) := by
  let instr := S.endpoints
  induction p with
  | tree t => exact tree_wf S t hp hΓ hslots _
  | unit => exact .unit _ _
  | pair p q ihp ihq => exact .pair (ihp hp.1) (ihq hp.2)
  | inl p ih => exact .inl (ih hp)
  | inr q ih => exact .inr (ih hp)

theorem value_arguments {k : Nat} {as : Fin k → α} (p : Value S slots (input k as))
    (hp : p.Pure (ε := ε) S) :
    ∃ ts : (i : Fin k) → Tree S slots (as i),
      (∀ i, DeclaredPure (ε := ε) S (ts i)) ∧
      p.source S = sourceTuple k (fun i => (ts i).source) := by
  induction k with
  | zero =>
    cases p
    exact ⟨fun i => i.elim0, fun i => i.elim0, rfl⟩
  | succ k ih =>
    cases p with
    | pair head tail =>
      cases head with
      | tree t =>
        obtain ⟨ts, hts, hs⟩ := ih tail hp.2
        refine ⟨Fin.cases (motive := fun i => Tree S slots (as i)) t ts,
          Fin.cases (motive := fun i => DeclaredPure (ε := ε) S
            (Fin.cases (motive := fun i => Tree S slots (as i)) t ts i)) hp.1 hts, ?_⟩
        exact congrArg (Expr.pair t.source) hs

def consSub (p : Expr Φ) (σ : Nat → Expr Φ) : Nat → Expr Φ
  | 0 => p
  | i + 1 => σ i

theorem subst_lift_beta (b p : Expr Φ) (σ : Nat → Expr Φ) :
    (b.subst (Expr.liftSubst σ)).subst p.subst0 = b.subst (consSub p σ) := by
  rw [subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact subst0_wk0 _ _


theorem subst_two_beta (c p q : Expr Φ) (σ : Nat → Expr Φ) :
    (((c.subst (Expr.liftSubst (Expr.liftSubst σ))).subst (Expr.liftSubst p.subst0)).subst q.subst0) =
      c.subst (consSub q (consSub p σ)) := by
  calc
    _ = (((c.subst (Expr.liftSubst (Expr.liftSubst σ))).subst q.wk0.subst0).subst p.subst0) := by
      simpa only [subst0_wk0] using
        (subst0_subst q.wk0 (c.subst (Expr.liftSubst (Expr.liftSubst σ))) p.subst0).symm
    _ = _ := by
      rw [subst_lift_beta, subst_subst]
      congr 1
      funext i
      cases i with
      | zero => exact subst0_wk0 _ _
      | succ j =>
        cases j with
        | zero => rfl
        | succ j => exact subst0_wk0 _ _

def NormalEnv (Δ : EffectCtx (Ty α) ε) (σ : Nat → Expr Φ) : Prop :=
  ∀ i : Fin Δ.length, ∃ p : Value S slots (Δ.get i).1,
    p.Pure (ε := ε) S ∧ σ i.val = p.source S

theorem normalEnv_cons {Δ : EffectCtx (Ty α) ε} {σ : Nat → Expr Φ}
    (hσ : NormalEnv (slots := slots) S Δ σ) {A : Ty α}
    (v : Value S slots A) (hv : v.Pure (ε := ε) S) :
    NormalEnv (slots := slots) S ((A, ⊥) :: Δ) (consSub (v.source S) σ) := by
  intro i
  exact Fin.cases (motive := fun j =>
    ∃ p : Value S slots (((A, (⊥ : ε)) :: Δ).get j).1,
      p.Pure (ε := ε) S ∧ consSub (v.source S) σ j.val = p.source S)
    ⟨v, hv, rfl⟩ (fun j => hσ j) i

theorem normalEnv_typed {Δ : EffectCtx (Ty α) ε} {σ : Nat → Expr Φ}
    (hσ : NormalEnv (slots := slots) S Δ σ) (hΓ : Γ.Pure)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) :
    letI := S.endpoints
    Source.Proofs.TypedSubst Γ Δ σ := by
  let instr := S.endpoints
  intro i
  obtain ⟨p, hp, he⟩ := hσ i
  rw [he]
  exact wf_wkEff (value_wf S p hp hΓ hslots) bot_le

theorem let2_beta_pair {A B C : Ty α} {e : ε}
    {p q c : Expr Φ}
    (hp : letI := S.endpoints; Wf Γ p A (⊥ : ε))
    (hq : letI := S.endpoints; Wf Γ q B (⊥ : ε))
    (hc : letI := S.endpoints; Wf ((B, ⊥) :: (A, ⊥) :: Γ) c C e) :
    letI := S.endpoints
    Eqv Γ C e (.let₂ (.pair p q) c) ((c.subst (Expr.liftSubst p.subst0)).subst q.subst0) := by
  let instr := S.endpoints
  have hq' := wf_wk (wf_wkEff hq (show (⊥ : ε) ≤ e from bot_le)) (Renaming.wk0 Γ (A, ⊥))
  have hp' := wf_wkEff hp (show (⊥ : ε) ≤ e from bot_le)
  have hq'' := wf_wkEff hq (show (⊥ : ε) ≤ e from bot_le)
  have rewrite : Eqv Γ C e (.let₂ (.pair p q) c) (.let₁ p (.let₁ q.wk0 c)) :=
    .step (.rewrite (.let₂ (.pair hp' hq'') hc) (.let₁ hp' (.let₁ hq' hc)) (.let2_pair _ _ _))
  have beta : Eqv Γ C e (.let₁ p (.let₁ q.wk0 c)) (.let₁ q (c.subst (Expr.liftSubst p.subst0))) := by
    have h := Eqv.step (Step.let1_beta hp (.let₁ hq' hc))
    change Eqv Γ C e (.let₁ p (.let₁ q.wk0 c))
      (.let₁ (q.wk0.subst p.subst0) (c.subst (Expr.liftSubst p.subst0))) at h
    simpa only [subst0_wk0] using h
  have hc' := wf_subst hc ((Source.Proofs.TypedSubst.subst0 hp).lift (B, ⊥))
  exact rewrite.trans (beta.trans (.step (.let1_beta hq hc')))

theorem normalize_subst {Δ : EffectCtx (Ty α) ε} {a : Expr Φ} {A : Ty α} {lo : ε}
    (h : letI := S.endpoints; Wf Δ a A lo) (hlo : lo = ⊥)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    {σ : Nat → Expr Φ} (hσ : NormalEnv (slots := slots) S Δ σ) :
    letI := S.endpoints
    ∃ p : Value S slots A, p.Pure (ε := ε) S ∧ Eqv Γ A e (a.subst σ) (p.source S) := by
  let instr := S.endpoints
  induction h generalizing σ with
  | var i hle =>
    obtain ⟨p, hp, he⟩ := hσ i
    refine ⟨p, hp, ?_⟩
    simpa only [Expr.subst, he] using
      Eqv.refl (wf_wkEff (value_wf S p hp hΓ hslots) (show (⊥ : ε) ≤ e from bot_le))
  | @op Δ f a lo hf ha ih =>
    obtain ⟨p, hp, he⟩ := ih hlo hσ
    have hf' : IsPure (⊥ : ε) f := le_antisymm (hlo ▸ hf) bot_le
    change Value S slots (input (S.arity f) (S.arg f)) at p
    obtain ⟨ts, hts, hrepr⟩ := value_arguments S p hp
    refine ⟨.tree (.op f ts), ⟨hf', hts⟩, ?_⟩
    exact Eqv.op (hf'.le.trans bot_le) (hrepr ▸ he)
  | @let₁ Δ a b A B lo ha hb iha ihb =>
    obtain ⟨p, hp, he⟩ := iha hlo hσ
    have hTyped := normalEnv_typed S hσ hΓ hslots
    have hb' := wf_wkEff (wf_subst hb (hTyped.lift (A, ⊥))) (hlo.symm ▸ bot_le : lo ≤ e)
    obtain ⟨v, hv, hn⟩ := ihb hlo (normalEnv_cons S hσ p hp)
    have beta := Eqv.step (Step.let1_beta (value_wf S p hp hΓ hslots) hb')
    rw [subst_lift_beta] at beta
    exact ⟨v, hv, (Eqv.let1 he (.refl hb')).trans (beta.trans hn)⟩
  | @pair Δ a b A B lo ha hb iha ihb =>
    obtain ⟨p, hp, hl⟩ := iha hlo hσ
    obtain ⟨q, hq, hr⟩ := ihb hlo hσ
    exact ⟨.pair p q, ⟨hp, hq⟩, Eqv.pair hl hr⟩
  | unit Δ lo =>
    exact ⟨.unit, trivial, .refl (.unit _ _)⟩
  | @let₂ Δ a c A B C lo ha hc iha ihc =>
    obtain ⟨p, hp, he⟩ := iha hlo hσ
    cases p with
    | pair p q =>
      have hTyped := normalEnv_typed S hσ hΓ hslots
      have hc' := wf_wkEff (wf_subst hc ((hTyped.lift (A, ⊥)).lift (B, ⊥)))
        (hlo.symm ▸ bot_le : lo ≤ e)
      obtain ⟨v, hv, hn⟩ := ihc hlo (normalEnv_cons S (normalEnv_cons S hσ p hp.1) q hp.2)
      have beta := let2_beta_pair S (value_wf S p hp.1 hΓ hslots) (value_wf S q hp.2 hΓ hslots) hc'
      rw [subst_two_beta] at beta
      exact ⟨v, hv, (Eqv.let2 he (.refl hc')).trans (beta.trans hn)⟩
  | inl ha ih =>
    obtain ⟨p, hp, he⟩ := ih hlo hσ
    exact ⟨.inl p, hp, .inl he⟩
  | inr hb ih =>
    obtain ⟨q, hq, he⟩ := ih hlo hσ
    exact ⟨.inr q, hq, .inr he⟩
  | @case Δ a l r A B C lo ha hl hr iha ihl ihr =>
    obtain ⟨p, hp, he⟩ := iha hlo hσ
    have hTyped := normalEnv_typed S hσ hΓ hslots
    have hl' := wf_wkEff (wf_subst hl (hTyped.lift (A, ⊥))) (hlo.symm ▸ bot_le : lo ≤ e)
    have hr' := wf_wkEff (wf_subst hr (hTyped.lift (B, ⊥))) (hlo.symm ▸ bot_le : lo ≤ e)
    have hCase := Eqv.case he (.refl hl') (.refl hr')
    cases p with
    | inl p =>
      obtain ⟨v, hv, hn⟩ := ihl hlo (normalEnv_cons S hσ p hp)
      have hpb := value_wf S p hp hΓ hslots
      have hp' := wf_wkEff hpb (show (⊥ : ε) ≤ e from bot_le)
      have step := Eqv.step (Step.reduce (.case (B := B) (.inl hp') hl' hr') (.let₁ hp' hl')
        (.case_inl _ _ _))
      have beta := Eqv.step (Step.let1_beta hpb hl')
      rw [subst_lift_beta] at beta
      exact ⟨v, hv, hCase.trans (step.trans (beta.trans hn))⟩
    | inr q =>
      obtain ⟨v, hv, hn⟩ := ihr hlo (normalEnv_cons S hσ q hp)
      have hqb := value_wf S q hp hΓ hslots
      have hq' := wf_wkEff hqb (show (⊥ : ε) ≤ e from bot_le)
      have step := Eqv.step (Step.reduce (.case (A := A) (.inr hq') hl' hr') (.let₁ hq' hr')
        (.case_inr _ _ _))
      have beta := Eqv.step (Step.let1_beta hqb hr')
      rw [subst_lift_beta] at beta
      exact ⟨v, hv, hCase.trans (step.trans (beta.trans hn))⟩
  | abort _ ih =>
    obtain ⟨p, _, _⟩ := ih hlo hσ
    cases p


theorem normalEnv_id (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) :
    NormalEnv (slots := slots) S Γ Expr.var := by
  intro i
  have witness {A : Ty α} (h : A = .base (slots i)) :
      ∃ p : Value S slots A, p.Pure (ε := ε) S ∧ (Expr.var i.val : Expr Φ) = p.source S := by
    subst A
    exact ⟨.tree (.var i), trivial, rfl⟩
  exact witness (hslots i)

public theorem normalize {a : Expr Φ} {A : Ty α}
    (h : letI := S.endpoints; Wf Γ a A (⊥ : ε))
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε) :
    letI := S.endpoints
    ∃ p : Value S slots A, p.Pure (ε := ε) S ∧ Eqv Γ A e a (p.source S) := by
  simpa only [subst_var] using normalize_subst S h rfl hΓ hslots e (normalEnv_id S hslots)

public theorem normalizesToTree {a : Expr Φ} {C : α}
    (h : letI := S.endpoints; Wf Γ a (.base C) (⊥ : ε))
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε) :
    SumSplit.NormalizesToTree S Γ slots e C a := by
  obtain ⟨p, hp, he⟩ := normalize S h hΓ hslots e
  cases p with | tree t => exact ⟨t, hp, he⟩

variable [DecidableEq α] [EffectIteration ε]

/-- Reflection for bottom-typed expressions in a pure atomic context. -/
public theorem endpoint_reflection_atomic {a b : Expr Φ} {C : α}
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (ha : letI := S.endpoints; Wf Γ a (.base C) (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ b (.base C) (⊥ : ε))
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base C) ↔
      Eqv Γ (.base C) e a b := by
  let instr := S.endpoints
  constructor
  · intro hn
    exact SumSplit.eqv_of_native_of_tree_normal_forms S hΓ hslots ht hs hn
      (normalizesToTree S ha hΓ hslots e) (normalizesToTree S hb hΓ hslots e)
  · intro h
    exact h.toLetIter ht hs

/-- A single open sum with atomic payloads can be at any slot. The branch
witnesses are derived from bottom-effect source typing. -/
public theorem endpoint_reflection_sum {a b : Expr Φ} {A B C : α}
    (i : Fin Γ.length) (hΓ : Γ.Pure)
    (hi : (Γ.get i).1 = .coprod (.base A) (.base B))
    (slotsL : Fin (SumSplit.branchCtx Γ i (.base A)).length → α)
    (slotsR : Fin (SumSplit.branchCtx Γ i (.base B)).length → α)
    (hslotsL : ∀ j, ((SumSplit.branchCtx Γ i (.base A)).get j).1 = .base (slotsL j))
    (hslotsR : ∀ j, ((SumSplit.branchCtx Γ i (.base B)).get j).1 = .base (slotsR j))
    (e : ε)
    (ha : letI := S.endpoints; Wf Γ a (.base C) (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ b (.base C) (⊥ : ε))
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base C) ↔
      Eqv Γ (.base C) e a b := by
  let instr := S.endpoints
  obtain ⟨haL, haR⟩ := SumSplit.wf_specializations i hi (hΓ i) ha
  obtain ⟨hbL, hbR⟩ := SumSplit.wf_specializations i hi (hΓ i) hb
  have hpL := SumSplit.branchCtx_pure hΓ i (.base A)
  have hpR := SumSplit.branchCtx_pure hΓ i (.base B)
  exact SumSplit.endpoint_reflection S i hΓ hi slotsL slotsR hslotsL hslotsR
    (wf_wkEff ha bot_le) (wf_wkEff hb bot_le) ht hs
    (normalizesToTree S haL hpL hslotsL e)
    (normalizesToTree S hbL hpL hslotsL e)
    (normalizesToTree S haR hpR hslotsR e)
    (normalizesToTree S hbR hpR hslotsR e)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Proofs
