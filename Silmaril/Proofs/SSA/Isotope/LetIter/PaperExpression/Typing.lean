module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Defs

set_option backward.isDefEq.respectTransparency false

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Proofs

open LocallyNameless (Tm HasType HasEffect HasTypeEffect Pure)

variable {τ : Type u} {Φ : Type v} {ε : Type w}

public theorem EffectCtx.get_toBoundCtx (Γ : EffectCtx τ ε) (i : Fin Γ.length) :
    Γ.toBoundCtx.get i = (Γ.get i).1 := by
  induction Γ with
  | nil => exact i.elim0
  | cons slot rest ih =>
    obtain ⟨A, effect⟩ := slot
    refine Fin.cases rfl (fun j => ?_) i
    exact ih j

private theorem EffectCtx.Pure.cons_bot [Bot ε] {Γ : EffectCtx τ ε} (h : Γ.Pure) (A : τ) :
    EffectCtx.Pure ((A, (⊥ : ε)) :: Γ) := by
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  exact h j

section Comparison

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : EffectCtx τ ε} {a : Expr Φ} {e : ε} {A : τ}

private theorem lower_wf (h : Wf Γ a A e) :
    ∃ t, a.toLetIter Γ.length = some t ∧
      HasTypeEffect (.nil : Ctx Empty τ) Γ.toBoundCtx t A e ∧ (e = ⊥ → Pure (⊥ : ε) t) := by
  induction h with
  | var i hi =>
    exact ⟨.bv i, by simp [Expr.toLetIter, i.isLt],
      ⟨EffectCtx.get_toBoundCtx _ i ▸ .bv, bot_le⟩, fun _ => .bv⟩
  | op hf _ ih =>
    obtain ⟨t, ht, typedT, pureT⟩ := ih
    exact ⟨.op _ t, by simp [Expr.toLetIter, ht], ⟨.op typedT.1, sup_le hf typedT.2⟩, fun he =>
      .op (le_bot_iff.mp (he ▸ hf)) (pureT he)⟩
  | let₁ _ _ ih₁ ih₂ =>
    obtain ⟨t, ht, typedT, pureT⟩ := ih₁
    obtain ⟨s, hs, typedS, pureS⟩ := ih₂
    simp only [List.length_cons] at hs
    exact ⟨.let₁ t s, by simp [Expr.toLetIter, ht, hs],
      ⟨.let₁ typedT.1 typedS.1, sup_le typedT.2 typedS.2⟩, fun he => .let₁ (pureT he) (pureS he)⟩
  | pair _ _ ih₁ ih₂ =>
    obtain ⟨t, ht, typedT, pureT⟩ := ih₁
    obtain ⟨s, hs, typedS, pureS⟩ := ih₂
    exact ⟨.pair t s, by simp [Expr.toLetIter, ht, hs],
      ⟨.pair typedT.1 typedS.1, sup_le typedT.2 typedS.2⟩, fun he => .pair (pureT he) (pureS he)⟩
  | unit => exact ⟨.unit, rfl, ⟨.unit, bot_le⟩, fun _ => .unit⟩
  | let₂ _ _ ih₁ ih₂ =>
    obtain ⟨t, ht, typedT, pureT⟩ := ih₁
    obtain ⟨s, hs, typedS, pureS⟩ := ih₂
    simp only [List.length_cons] at hs
    exact ⟨.let₂ t s, by simp [Expr.toLetIter, ht, hs],
      ⟨.let₂ typedT.1 typedS.1, sup_le typedT.2 typedS.2⟩, fun he => .let₂ (pureT he) (pureS he)⟩
  | inl _ ih =>
    obtain ⟨t, ht, typedT, pureT⟩ := ih
    exact ⟨.inl t, by simp [Expr.toLetIter, ht], ⟨.inl typedT.1, typedT.2⟩, fun he => .inl (pureT he)⟩
  | inr _ ih =>
    obtain ⟨t, ht, typedT, pureT⟩ := ih
    exact ⟨.inr t, by simp [Expr.toLetIter, ht], ⟨.inr typedT.1, typedT.2⟩, fun he => .inr (pureT he)⟩
  | case _ _ _ ih₁ ih₂ ih₃ =>
    obtain ⟨t, ht, typedT, pureT⟩ := ih₁
    obtain ⟨l, hl, typedL, pureL⟩ := ih₂
    obtain ⟨r, hr, typedR, pureR⟩ := ih₃
    simp only [List.length_cons] at hl hr
    exact ⟨.case t l r, by simp [Expr.toLetIter, ht, hl, hr],
      ⟨.case typedT.1 typedL.1 typedR.1, sup_le typedT.2 (sup_le typedL.2 typedR.2)⟩,
      fun he => .case (pureT he) (pureL he) (pureR he)⟩
  | abort _ ih =>
    obtain ⟨t, ht, typedT, pureT⟩ := ih
    exact ⟨.abort t, by simp [Expr.toLetIter, ht], ⟨.abort typedT.1, typedT.2⟩, fun he => .abort (pureT he)⟩

/-- Forgetting ambient slot effects preserves typing at the original effect bound. -/
public theorem Wf.toLetIter (h : Wf Γ a A e) :
    ∃ t, a.toLetIter Γ.length = some t ∧ HasTypeEffect (.nil : Ctx Empty τ) Γ.toBoundCtx t A e := by
  obtain ⟨t, lowered, typed, _⟩ := lower_wf h
  exact ⟨t, lowered, typed⟩

/-- The translation of a bottom-effect source expression is syntactically pure. -/
public theorem Wf.pure_toLetIter (h : Wf Γ a A (⊥ : ε)) {t : Tm Empty Φ Γ.length}
    (lowered : a.toLetIter Γ.length = some t) : Pure (⊥ : ε) t := by
  obtain ⟨s, lowerS, _, pureS⟩ := lower_wf h
  rw [lowerS] at lowered
  exact (Option.some.inj lowered) ▸ pureS rfl

/-- Recover effect-indexed source typing when every ambient slot is pure. -/
public theorem Wf.ofLetIter {t : Tm Empty Φ Γ.length} (pureCtx : Γ.Pure)
    (lowered : a.toLetIter Γ.length = some t)
    (typed : HasTypeEffect (.nil : Ctx Empty τ) Γ.toBoundCtx t A e) :
    Wf Γ a A e := by
  obtain ⟨typing, effect⟩ := typed
  induction a generalizing Γ A with
  | var i =>
    by_cases hi : i < Γ.length
    · simp only [Expr.toLetIter, dite_eq_left hi, Option.some.injEq] at lowered
      subst t
      cases typing
      exact (EffectCtx.get_toBoundCtx Γ ⟨i, hi⟩).symm ▸ Wf.var ⟨i, hi⟩ (by rw [pureCtx]; exact bot_le)
    · simp [Expr.toLetIter, hi] at lowered
  | op f a ih =>
    simp only [Expr.toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    cases typing with
    | op typingArg =>
      obtain ⟨hf, ha⟩ := LocallyNameless.hasEffect_op_iff.mp effect
      exact .op hf (ih pureCtx loweredArg typingArg ha)
  | let₁ a b iha ihb =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, body, loweredBody, rfl⟩ := lowered
    cases typing with
    | let₁ ta tb =>
      obtain ⟨ea, eb⟩ := sup_le_iff.mp effect
      exact .let₁ (iha pureCtx loweredArg ta ea)
        (ihb (EffectCtx.Pure.cons_bot pureCtx _) loweredBody tb eb)
  | pair a b iha ihb =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨left, loweredLeft, right, loweredRight, rfl⟩ := lowered
    cases typing with
    | pair tl tr =>
      obtain ⟨el, er⟩ := sup_le_iff.mp effect
      exact .pair (iha pureCtx loweredLeft tl el) (ihb pureCtx loweredRight tr er)
  | unit =>
    simp only [Expr.toLetIter, Option.some.injEq] at lowered
    subst t
    cases typing
    exact .unit Γ e
  | let₂ a b iha ihb =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, body, loweredBody, rfl⟩ := lowered
    cases typing with
    | let₂ ta tb =>
      obtain ⟨ea, eb⟩ := sup_le_iff.mp effect
      exact .let₂ (iha pureCtx loweredArg ta ea)
        (ihb (EffectCtx.Pure.cons_bot (EffectCtx.Pure.cons_bot pureCtx _) _) loweredBody tb eb)
  | inl a ih =>
    simp only [Expr.toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    cases typing with
    | inl ta => exact .inl (ih pureCtx loweredArg ta effect)
  | inr a ih =>
    simp only [Expr.toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    cases typing with
    | inr ta => exact .inr (ih pureCtx loweredArg ta effect)
  | case a l r iha ihl ihr =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, left, loweredLeft, right, loweredRight, rfl⟩ := lowered
    cases typing with
    | case ta tl tr =>
      obtain ⟨ea, hlr⟩ := sup_le_iff.mp effect
      obtain ⟨el, er⟩ := sup_le_iff.mp hlr
      exact .case (iha pureCtx loweredArg ta ea)
        (ihl (EffectCtx.Pure.cons_bot pureCtx _) loweredLeft tl el)
        (ihr (EffectCtx.Pure.cons_bot pureCtx _) loweredRight tr er)
  | abort a ih =>
    simp only [Expr.toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    cases typing with
    | abort ta => exact .abort (ih pureCtx loweredArg ta effect)

end Comparison

end Silmaril.Isotope.LetIter.PaperExpression.Proofs
