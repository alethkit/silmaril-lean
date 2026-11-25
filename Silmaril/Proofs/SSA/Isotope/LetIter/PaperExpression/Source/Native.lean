module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Equations.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Native.Rewrites

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.NativeProofs

open LocallyNameless (Tm HasType HasTypeEffect Pure PureTypedSubst Equiv AbortEquiv Refinement)

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  {Γ : EffectCtx τ ε} {A : τ} {a b : Expr Φ}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

private theorem initialType_empty {pe : ε} {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n}
    (h : InitialType A) (ht : HasType Φ Γ₀ β t A) (pt : Pure pe t) :
    ∃ s : Tm Empty Φ n, HasType Φ Γ₀ β s empty ∧ Pure pe s := by
  induction h generalizing n with
  | empty => exact ⟨t, ht, pt⟩
  | @product_left X Y _ ih =>
    obtain ⟨s, hs, ps⟩ := ih (β := .snoc (.snoc β X) Y) (t := .bv 1) .bv .bv
    exact ⟨.let₂ t s, .let₂ ht hs, .let₂ pt ps⟩
  | @product_right X Y _ ih =>
    obtain ⟨s, hs, ps⟩ := ih (β := .snoc (.snoc β X) Y) (t := .bv 0) .bv .bv
    exact ⟨.let₂ t s, .let₂ ht hs, .let₂ pt ps⟩
  | @coprod X Y _ _ ihX ihY =>
    obtain ⟨l, hl, pl⟩ := ihX (β := .snoc β X) (t := .bv 0) .bv .bv
    obtain ⟨r, hr, pr⟩ := ihY (β := .snoc β Y) (t := .bv 0) .bv .bv
    exact ⟨.case t l r, .case ht hl hr, .case pt pl pr⟩

private theorem equiv_of_pure_empty {pe : ε} {n : Nat} {β : BoundCtx τ n}
    {t s impossible : Tm Empty Φ n}
    (ht : HasType Φ Γ₀ β t A) (hs : HasType Φ Γ₀ β s A)
    (hi : HasType Φ Γ₀ β impossible empty) (pi : Pure pe impossible) :
    Equiv pe Γ₀ β t s A := by
  let abortToUnit := HasType.abort (C := (unit : τ)) hi
  have dropUnused (r : Tm Empty Φ n) : r.lift.instantiate (.abort impossible) = r := by
    unfold Tm.instantiate Tm.lift
    rw [Tm.bsubst_rename]
    exact Tm.bsubst_id r
  have left : Equiv pe Γ₀ β (.let₁ (.abort impossible) t.lift) t A := by
    simpa only [dropUnused] using Equiv.letBeta (.abort pi) abortToUnit ht.lift
  have right : Equiv pe Γ₀ β (.let₁ (.abort impossible) s.lift) s A := by
    simpa only [dropUnused] using Equiv.letBeta (.abort pi) abortToUnit hs.lift
  exact left.symm.trans ((Equiv.emptyInitial (A := (unit : τ)) hi ht.lift hs.lift).trans right)

private theorem equiv_unit_of_pure {pe : ε} {n : Nat} {β : BoundCtx τ n}
    {t s : Tm Empty Φ n}
    (ht : HasType Φ Γ₀ β t unit) (hs : HasType Φ Γ₀ β s unit)
    (pt : Pure pe t) (ps : Pure pe s) :
    Equiv pe Γ₀ β t s (unit : τ) :=
  ((Equiv.unitEta ht).symm.trans (Equiv.letBeta pt ht .unit)).trans
    (((Equiv.unitEta hs).symm.trans (Equiv.letBeta ps hs .unit)).symm)

variable [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}

private def LoweredEqv (Γ : EffectCtx τ ε) (A : τ) (a b : Expr Φ) : Prop :=
  ∃ t s, a.toLetIter Γ.length = some t ∧ b.toLetIter Γ.length = some s ∧
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s A

private theorem lower_step (h : Step Γ A e a b) : LoweredEqv Γ A a b := by
  cases h with
  | let1_beta ha hb =>
    obtain ⟨_, h₁, _⟩ := ha.toLetIter
    obtain ⟨_, h₂, _⟩ := hb.toLetIter
    obtain ⟨l, r, _, _, h⟩ := let1_beta_toLetIter ha hb h₁ h₂
    exact ⟨_, _, l, r, .equiv h⟩
  | rewrite ha hb h =>
    obtain ⟨_, hl, ht⟩ := ha.toLetIter
    obtain ⟨_, hr, hs⟩ := hb.toLetIter
    exact ⟨_, _, hl, hr, rewrite_toLetIter h hl hr ht.1 hs.1⟩
  | reduce ha hb h =>
    obtain ⟨_, hl, ht⟩ := ha.toLetIter
    obtain ⟨_, hr, hs⟩ := hb.toLetIter
    exact ⟨_, _, hl, hr, .equiv (reduce_toLetIter h hl hr ht.1 hs.1)⟩
  | initial hi ha hb =>
    obtain ⟨_, hl, ht⟩ := ha.toLetIter
    obtain ⟨_, hr, hs⟩ := hb.toLetIter
    obtain ⟨i, hi, _⟩ := hi
    have hv : HasType Φ Γ₀ Γ.toBoundCtx (.bv i) (Γ.get i).1 :=
      EffectCtx.get_toBoundCtx Γ i ▸ HasType.bv
    obtain ⟨_, hz, pz⟩ := initialType_empty (pe := (⊥ : ε)) hi hv .bv
    exact ⟨_, _, hl, hr, .equiv (equiv_of_pure_empty ht.1 hs.1 hz pz)⟩
  | terminal ha hb =>
    obtain ⟨_, hl, ht⟩ := ha.toLetIter
    obtain ⟨_, hr, hs⟩ := hb.toLetIter
    exact ⟨_, _, hl, hr, .equiv (equiv_unit_of_pure ht.1 hs.1
      (ha.pure_toLetIter hl) (hb.pure_toLetIter hr))⟩

private theorem lower_eqv (h : Eqv Γ A e a b) : LoweredEqv Γ A a b := by
  induction h with
  | step h => exact lower_step h
  | refl h =>
    obtain ⟨_, hl, ht⟩ := h.toLetIter
    exact ⟨_, _, hl, hl, Refinement.refl ht.1⟩
  | symm _ ih =>
    obtain ⟨_, _, hl, hr, h⟩ := ih
    exact ⟨_, _, hr, hl, h.symm⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨_, t, hl, hm, h₁⟩ := ih₁
    obtain ⟨s, _, hm', hr, h₂⟩ := ih₂
    have hts := Option.some.inj (hm.symm.trans hm')
    subst s
    exact ⟨_, _, hl, hr, .trans h₁ h₂⟩
  | op _ _ ih =>
    obtain ⟨_, _, hl, hr, h⟩ := ih
    exact ⟨_, _, by simp [Expr.toLetIter, hl], by simp [Expr.toLetIter, hr], .op h⟩
  | let1 _ _ ih₁ ih₂ =>
    obtain ⟨_, _, hl, hr, h₁⟩ := ih₁
    obtain ⟨_, _, hl', hr', h₂⟩ := ih₂
    simp only [List.length_cons] at hl' hr'
    exact ⟨_, _, by simp [Expr.toLetIter, hl, hl'], by simp [Expr.toLetIter, hr, hr'], .let₁ h₁ h₂⟩
  | pair _ _ ih₁ ih₂ =>
    obtain ⟨_, _, hl, hr, h₁⟩ := ih₁
    obtain ⟨_, _, hl', hr', h₂⟩ := ih₂
    exact ⟨_, _, by simp [Expr.toLetIter, hl, hl'], by simp [Expr.toLetIter, hr, hr'], .pair h₁ h₂⟩
  | let2 _ _ ih₁ ih₂ =>
    obtain ⟨_, _, hl, hr, h₁⟩ := ih₁
    obtain ⟨_, _, hl', hr', h₂⟩ := ih₂
    simp only [List.length_cons] at hl' hr'
    exact ⟨_, _, by simp [Expr.toLetIter, hl, hl'], by simp [Expr.toLetIter, hr, hr'], .let₂ h₁ h₂⟩
  | inl _ ih =>
    obtain ⟨_, _, hl, hr, h⟩ := ih
    exact ⟨_, _, by simp [Expr.toLetIter, hl], by simp [Expr.toLetIter, hr], .inl h⟩
  | inr _ ih =>
    obtain ⟨_, _, hl, hr, h⟩ := ih
    exact ⟨_, _, by simp [Expr.toLetIter, hl], by simp [Expr.toLetIter, hr], .inr h⟩
  | case _ _ _ ih₁ ih₂ ih₃ =>
    obtain ⟨_, _, hl, hr, h₁⟩ := ih₁
    obtain ⟨_, _, hl', hr', h₂⟩ := ih₂
    obtain ⟨_, _, hl'', hr'', h₃⟩ := ih₃
    simp only [List.length_cons] at hl' hr' hl'' hr''
    exact ⟨_, _, by simp [Expr.toLetIter, hl, hl', hl''], by simp [Expr.toLetIter, hr, hr', hr''],
      .case h₁ h₂ h₃⟩
  | abort _ ih =>
    obtain ⟨_, _, hl, hr, h⟩ := ih
    exact ⟨_, _, by simp [Expr.toLetIter, hl], by simp [Expr.toLetIter, hr], .abort h⟩

theorem eqv_toLetIter {t s : Tm Empty Φ Γ.length} (h : Eqv Γ A e a b)
    (hl : a.toLetIter Γ.length = some t) (hr : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s A := by
  obtain ⟨_, _, ht, hs, h⟩ := lower_eqv h
  exact Option.some.inj (ht.symm.trans hl) ▸ Option.some.inj (hs.symm.trans hr) ▸ h

/-- A typed source substitution from a bottom-annotated context lowers to a
pure native substitution. The existing native preservation theorem applies to
the entire derivation of the original equality. -/
theorem native_subst {Δ : EffectCtx τ ε} (hΓ : Γ.Pure)
    {σ : Nat → Expr Φ} {C : τ}
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (hn : AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) Γ.toBoundCtx t s C)
    (hσ : ∀ i : Fin Γ.length, Wf Δ (σ i.val) (Γ.get i).1 (Γ.get i).2) :
    ∃ t' s' : Tm Empty Φ Δ.length,
      (a.subst σ).toLetIter Δ.length = some t' ∧
      (b.subst σ).toLetIter Δ.length = some s' ∧
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) Δ.toBoundCtx t' s' C := by
  classical
  have hw (i : Fin Γ.length) : Wf Δ (σ i.val) (Γ.get i).1 (⊥ : ε) := hΓ i ▸ hσ i
  choose θ hθ htyped using fun i => (hw i).toLetIter
  have sub : PureTypedSubst (⊥ : ε) (.nil : Ctx Empty τ) Γ.toBoundCtx Δ.toBoundCtx θ :=
    ⟨fun i => (EffectCtx.get_toBoundCtx Γ i).symm ▸ (htyped i).1,
      fun i => (hw i).pure_toLetIter (hθ i)⟩
  exact ⟨_, _, Expr.toLetIter_subst ht hθ, Expr.toLetIter_subst hs hθ, hn.bsubst sub⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.NativeProofs
