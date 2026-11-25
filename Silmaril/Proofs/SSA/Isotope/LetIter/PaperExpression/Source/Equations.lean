module

public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Substitution

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs

open Expr

variable {τ : Type u} {Φ : Type v} {ε : Type w}

private theorem wk0_subst_lift (a : Expr Φ) (σ : Nat → Expr Φ) :
    a.wk0.subst (liftSubst σ) = (a.subst σ).wk0 := by
  simp only [wk0, subst_wk, wk_subst]
  rfl

private theorem rewrite_subst {a b : Expr Φ} (h : Rewrite a b) (σ : Nat → Expr Φ) :
    Rewrite (a.subst σ) (b.subst σ) := by
  cases h <;>
    simp only [subst, wk0_subst_lift, wk1_subst_lift, wk2_subst_lift] <;>
    constructor

private theorem reduce_subst {a b : Expr Φ} (h : Reduce a b) (σ : Nat → Expr Φ) :
    Reduce (a.subst σ) (b.subst σ) := by
  cases h <;> constructor

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]

private theorem step_typed {Γ : EffectCtx τ ε} {A : τ} {e : ε} {a b : Expr Φ}
    (h : Step Γ A e a b) : Wf Γ a A e ∧ Wf Γ b A e := by
  cases h with
  | let1_beta ha hb => exact ⟨.let₁ (wf_wkEff ha bot_le) hb, wf_subst hb (TypedSubst.subst0 ha)⟩
  | rewrite ha hb _ | reduce ha hb _ | initial _ ha hb => exact ⟨ha, hb⟩
  | terminal ha hb => exact ⟨wf_wkEff ha bot_le, wf_wkEff hb bot_le⟩

theorem eqv_typed {Γ : EffectCtx τ ε} {A : τ} {e : ε} {a b : Expr Φ}
    (h : Eqv Γ A e a b) : Wf Γ a A e ∧ Wf Γ b A e := by
  induction h with
  | step h => exact step_typed h
  | refl h => exact ⟨h, h⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ihA ihB => exact ⟨ihA.1, ihB.2⟩
  | op hf _ ih => exact ⟨.op hf ih.1, .op hf ih.2⟩
  | let1 _ _ ihA ihB => exact ⟨.let₁ ihA.1 ihB.1, .let₁ ihA.2 ihB.2⟩
  | pair _ _ ihA ihB => exact ⟨.pair ihA.1 ihB.1, .pair ihA.2 ihB.2⟩
  | let2 _ _ ihA ihB => exact ⟨.let₂ ihA.1 ihB.1, .let₂ ihA.2 ihB.2⟩
  | inl _ ih => exact ⟨.inl ih.1, .inl ih.2⟩
  | inr _ ih => exact ⟨.inr ih.1, .inr ih.2⟩
  | case _ _ _ ihA ihL ihR => exact ⟨.case ihA.1 ihL.1 ihR.1, .case ihA.2 ihL.2 ihR.2⟩
  | abort _ ih => exact ⟨.abort ih.1, .abort ih.2⟩

private theorem step_wkEff {Γ : EffectCtx τ ε} {A : τ} {e hi : ε} {a b : Expr Φ}
    (d : Step Γ A e a b) (h : e ≤ hi) : Step Γ A hi a b := by
  cases d with
  | let1_beta ha hb => exact .let1_beta ha (wf_wkEff hb h)
  | rewrite ha hb hr => exact .rewrite (wf_wkEff ha h) (wf_wkEff hb h) hr
  | reduce ha hb hr => exact .reduce (wf_wkEff ha h) (wf_wkEff hb h) hr
  | initial hΓ ha hb => exact .initial hΓ (wf_wkEff ha h) (wf_wkEff hb h)
  | terminal ha hb => exact .terminal ha hb

theorem eqv_wkEff {Γ : EffectCtx τ ε} {A : τ} {e hi : ε} {a b : Expr Φ}
    (d : Eqv Γ A e a b) (h : e ≤ hi) : Eqv Γ A hi a b := by
  induction d generalizing hi with
  | step d => exact .step (step_wkEff d h)
  | refl d => exact .refl (wf_wkEff d h)
  | op hf _ ih => exact .op (hf.trans h) (ih h)
  | symm _ ih => exact .symm (ih h)
  | trans _ _ ihA ihB => exact .trans (ihA h) (ihB h)
  | let1 _ _ ihA ihB => exact .let1 (ihA h) (ihB h)
  | pair _ _ ihA ihB => exact .pair (ihA h) (ihB h)
  | let2 _ _ ihA ihB => exact .let2 (ihA h) (ihB h)
  | inl _ ih => exact .inl (ih h)
  | inr _ ih => exact .inr (ih h)
  | case _ _ _ ihA ihL ihR => exact .case (ihA h) (ihL h) (ihR h)
  | abort _ ih => exact .abort (ih h)

private theorem initialType_witness {Γ : EffectCtx τ ε} {A : τ} {a : Expr Φ}
    (h : InitialType A) (d : Wf Γ a A ⊥) : ∃ b : Expr Φ, Wf Γ b empty ⊥ := by
  induction h generalizing Γ a with
  | empty => exact ⟨a, d⟩
  | @product_left A B _ ih =>
    have var : Wf ((B, ⊥) :: (A, ⊥) :: Γ) (.var 1 : Expr Φ) A ⊥ :=
      .var ⟨1, by simp⟩ bot_le
    obtain ⟨b, hb⟩ := ih var
    exact ⟨.let₂ a b, .let₂ d hb⟩
  | @product_right A B _ ih =>
    have var : Wf ((B, ⊥) :: (A, ⊥) :: Γ) (.var 0 : Expr Φ) B ⊥ :=
      .var 0 bot_le
    obtain ⟨b, hb⟩ := ih var
    exact ⟨.let₂ a b, .let₂ d hb⟩
  | @coprod A B _ _ ihL ihR =>
    have varL : Wf ((A, ⊥) :: Γ) (.var 0 : Expr Φ) A ⊥ := .var 0 bot_le
    have varR : Wf ((B, ⊥) :: Γ) (.var 0 : Expr Φ) B ⊥ := .var 0 bot_le
    obtain ⟨l, hl⟩ := ihL varL
    obtain ⟨r, hr⟩ := ihR varR
    exact ⟨.case a l r, .case d hl hr⟩

private theorem initialContext_witness {Γ : EffectCtx τ ε}
    (h : InitialContext Γ) : ∃ a : Expr Φ, Wf Γ a empty ⊥ := by
  obtain ⟨i, ht, he⟩ := h
  exact initialType_witness ht (.var i (he.le))

theorem eqv_initial_of_empty {Γ : EffectCtx τ ε} {A : τ} {e : ε} {a b c : Expr Φ}
    (hc : Wf Γ c empty ⊥) (ha : Wf Γ a A e) (hb : Wf Γ b A e) : Eqv Γ A e a b := by
  let slot : τ × ε := (empty, ⊥)
  have ha' : Wf (slot :: Γ) a.wk0 A e := wf_wk ha (Renaming.wk0 Γ slot)
  have hb' : Wf (slot :: Γ) b.wk0 A e := wf_wk hb (Renaming.wk0 Γ slot)
  have hΓ : InitialContext (slot :: Γ) := ⟨0, .empty, rfl⟩
  have dropA : Eqv Γ A e (.let₁ c a.wk0) a := by
    simpa only [subst0_wk0] using Eqv.step (Step.let1_beta hc ha')
  have dropB : Eqv Γ A e (.let₁ c b.wk0) b := by
    simpa only [subst0_wk0] using Eqv.step (Step.let1_beta hc hb')
  exact dropA.symm.trans ((Eqv.let1 (.refl (wf_wkEff hc bot_le)) (.step (.initial hΓ ha' hb'))).trans dropB)

private theorem step_subst {Γ Δ : EffectCtx τ ε} {σ : Nat → Expr Φ}
    {A : τ} {e : ε} {a b : Expr Φ} (h : Step Δ A e a b) (hs : TypedSubst Γ Δ σ) :
    Eqv Γ A e (a.subst σ) (b.subst σ) := by
  cases h with
  | let1_beta ha hb =>
    rw [subst0_subst]
    exact .step (.let1_beta (wf_subst ha hs) (wf_subst hb (hs.lift _)))
  | rewrite ha hb hr =>
    exact .step (.rewrite (wf_subst ha hs) (wf_subst hb hs) (rewrite_subst hr σ))
  | reduce ha hb hr =>
    exact .step (.reduce (wf_subst ha hs) (wf_subst hb hs) (reduce_subst hr σ))
  | initial hΔ ha hb =>
    obtain ⟨_, hc⟩ := initialContext_witness (Φ := Φ) hΔ
    exact eqv_initial_of_empty (wf_subst hc hs) (wf_subst ha hs) (wf_subst hb hs)
  | terminal ha hb => exact .step (.terminal (wf_subst ha hs) (wf_subst hb hs))

theorem eqv_subst {Γ Δ : EffectCtx τ ε} {σ : Nat → Expr Φ}
    {A : τ} {e : ε} {a b : Expr Φ} (h : Eqv Δ A e a b) (hs : TypedSubst Γ Δ σ) :
    Eqv Γ A e (a.subst σ) (b.subst σ) := by
  induction h generalizing Γ σ with
  | step h => exact step_subst h hs
  | refl d => exact .refl (wf_subst d hs)
  | symm _ ih => exact .symm (ih hs)
  | trans _ _ ihA ihB => exact .trans (ihA hs) (ihB hs)
  | op hf _ ih => exact .op hf (ih hs)
  | let1 _ _ ihA ihB => exact .let1 (ihA hs) (ihB (hs.lift _))
  | pair _ _ ihA ihB => exact .pair (ihA hs) (ihB hs)
  | let2 _ _ ihA ihB => exact .let2 (ihA hs) (ihB ((hs.lift _).lift _))
  | inl _ ih => exact .inl (ih hs)
  | inr _ ih => exact .inr (ih hs)
  | case _ _ _ ihA ihL ihR => exact .case (ihA hs) (ihL (hs.lift _)) (ihR (hs.lift _))
  | abort _ ih => exact .abort (ih hs)

theorem eqv_wk0 {Γ : EffectCtx τ ε} {A : τ} {e : ε} {a b : Expr Φ}
    (h : Eqv Γ A e a b) (slot : τ × ε) : Eqv (slot :: Γ) A e a.wk0 b.wk0 := by
  have hs : TypedSubst (slot :: Γ) Γ (Expr.var ∘ Nat.succ : Nat → Expr Φ) :=
    fun i => Wf.var (Γ := slot :: Γ) i.succ le_rfl
  simpa only [← subst_wk, subst_var, wk0] using eqv_subst h hs

/-- Two substitutions into the same context are related at the effects of the slots. -/
@[expose] def RelatedSubst (Γ Δ : EffectCtx τ ε) (σ θ : Nat → Expr Φ) : Prop :=
  ∀ i : Fin Δ.length, Eqv Γ (Δ.get i).1 (Δ.get i).2 (σ i.val) (θ i.val)

theorem RelatedSubst.lift {Γ Δ : EffectCtx τ ε} {σ θ : Nat → Expr Φ}
    (h : RelatedSubst Γ Δ σ θ) (slot : τ × ε) :
    RelatedSubst (slot :: Γ) (slot :: Δ) (liftSubst σ) (liftSubst θ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .refl (Wf.var 0 le_rfl)
  · exact eqv_wk0 (h j) slot

theorem eqv_subst_congr {Γ Δ : EffectCtx τ ε} {σ θ : Nat → Expr Φ}
    {A : τ} {e : ε} {a : Expr Φ} (h : Wf Δ a A e) (hs : RelatedSubst Γ Δ σ θ) :
    Eqv Γ A e (a.subst σ) (a.subst θ) := by
  induction h generalizing Γ σ θ with
  | var i hi => exact eqv_wkEff (hs i) hi
  | op hf _ ih => exact .op hf (ih hs)
  | let₁ _ _ ihA ihB => exact .let1 (ihA hs) (ihB (hs.lift _))
  | pair _ _ ihA ihB => exact .pair (ihA hs) (ihB hs)
  | unit _ e => exact .refl (.unit Γ e)
  | let₂ _ _ ihA ihB => exact .let2 (ihA hs) (ihB ((hs.lift _).lift _))
  | inl _ ih => exact .inl (ih hs)
  | inr _ ih => exact .inr (ih hs)
  | case _ _ _ ihA ihL ihR => exact .case (ihA hs) (ihL (hs.lift _)) (ihR (hs.lift _))
  | abort _ ih => exact .abort (ih hs)

end Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs
