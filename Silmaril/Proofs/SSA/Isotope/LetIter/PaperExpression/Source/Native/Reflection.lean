module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Categorical.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Substitution

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.NativeProofs

open LocallyNameless (Tm HasTypeEffect Pure CoreAxiom AbortSequence)

variable {τ : Type u} {Φ : Type v} {ε : Type w}

/-- Read back the constructors common to native LetIter and source expressions.
The inverse theorems use this operation only on loop-free terms. -/
private def readback : {n : Nat} → Tm Empty Φ n → Expr Φ
  | _, .fv x => x.elim
  | _, .bv i => .var i.val
  | _, .op f a => .op f (readback a)
  | _, .let₁ a b => .let₁ (readback a) (readback b)
  | _, .pair a b => .pair (readback a) (readback b)
  | _, .unit => .unit
  | _, .let₂ a b => .let₂ (readback a) (readback b)
  | _, .inl a => .inl (readback a)
  | _, .inr b => .inr (readback b)
  | _, .case a l r => .case (readback a) (readback l) (readback r)
  | _, .abort a => .abort (readback a)
  | _, .iter _ _ => .unit

private theorem lower_readback {n : Nat} {t : Tm Empty Φ n} (hl : LoopFree t) :
    (readback t).toLetIter n = some t := by
  induction t with
  | fv x => exact x.elim
  | bv i => simp [readback, Expr.toLetIter, i.isLt]
  | unit => rfl
  | iter => exact hl.elim
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp [readback, Expr.toLetIter, ih hl]
  | let₁ _ _ iha ihb | let₂ _ _ iha ihb | pair _ _ iha ihb =>
    simp [readback, Expr.toLetIter, iha hl.1, ihb hl.2]
  | case _ _ _ iha ihl ihr =>
    simp [readback, Expr.toLetIter, iha hl.1, ihl hl.2.1, ihr hl.2.2]

private theorem readback_lower {n : Nat} {a : Expr Φ} {t : Tm Empty Φ n}
    (hl : a.toLetIter n = some t) : readback t = a := by
  induction a generalizing n with
  | var i =>
    by_cases hi : i < n
    · simp only [Expr.toLetIter, dite_eq_left hi, Option.some.injEq] at hl
      subst t
      rfl
    · simp [Expr.toLetIter, hi] at hl
  | unit =>
    have h := Option.some.inj hl
    subst t
    rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [Expr.toLetIter, Option.map_eq_some_iff] at hl
    obtain ⟨_, hl, rfl⟩ := hl
    simp [readback, ih hl]
  | let₁ _ _ iha ihb | let₂ _ _ iha ihb | pair _ _ iha ihb =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hl
    obtain ⟨_, ha, _, hb, rfl⟩ := hl
    simp [readback, iha ha, ihb hb]
  | case _ _ _ iha ihl ihr =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hl
    obtain ⟨_, ha, _, hl, _, hr, rfl⟩ := hl
    simp [readback, iha ha, ihl hl, ihr hr]

private theorem readback_lift {n : Nat} {t : Tm Empty Φ n} (hl : LoopFree t) :
    readback t.lift = (readback t).wk0 :=
  readback_lower (Expr.toLetIter_wk0 (lower_readback hl))

private theorem readback_underBinder {n : Nat} {t : Tm Empty Φ (n + 1)} (hl : LoopFree t) :
    readback t.underBinder = (readback t).wk1 :=
  readback_lower (Expr.toLetIter_wk1 (lower_readback hl))

private theorem readback_underBinder₂ {n : Nat} {t : Tm Empty Φ (n + 1)} (hl : LoopFree t) :
    readback t.underBinder.underBinder = (readback t).wk1.wk1 :=
  readback_lower (Expr.toLetIter_wk1 (Expr.toLetIter_wk1 (lower_readback hl)))

private theorem readback_underTwoBinders {n : Nat} {t : Tm Empty Φ (n + 2)} (hl : LoopFree t) :
    readback t.underTwoBinders = (readback t).wk2 :=
  readback_lower (Expr.toLetIter_wk2 (lower_readback hl))

private theorem readback_instantiate {n : Nat} {t : Tm Empty Φ n} {s : Tm Empty Φ (n + 1)}
    (ht : LoopFree t) (hs : LoopFree s) :
    readback (s.instantiate t) = (readback s).subst (readback t).subst0 :=
  readback_lower (Expr.toLetIter_subst0 (lower_readback ht) (lower_readback hs))

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  {Γ : EffectCtx τ ε} {A X Y : τ} {a b c : Expr Φ} {e : ε}

section SourceRules

variable [Preorder ε] [OrderBot ε]

private theorem wf_var0 (Γ : EffectCtx τ ε) (A : τ) (e : ε) :
    Wf ((A, ⊥) :: Γ) (.var 0 : Expr Φ) A e :=
  .var (Γ := (A, ⊥) :: Γ) 0 bot_le

private theorem wf_wk1 (hb : Wf ((X, ⊥) :: Γ) b A e) (Y : τ) :
    Wf ((X, ⊥) :: (Y, ⊥) :: Γ) b.wk1 A e :=
  Proofs.wf_wk hb ((Proofs.Renaming.wk0 Γ (Y, ⊥)).lift (X, ⊥))

private theorem letEta (ha : Wf Γ a A e) : Eqv Γ A e (.let₁ a (.var 0)) a :=
  .step (.rewrite (.let₁ ha (wf_var0 Γ A e)) ha (.let1_eta a))

private theorem unitEta (ha : Wf Γ a unit e) : Eqv Γ unit e (.let₁ a .unit) a :=
  (Eqv.let1 (.refl ha)
    (.step (.terminal (.unit _ _) (wf_var0 Γ unit ⊥)))).trans (letEta ha)

private theorem source_commute_abort (ha : Wf Γ a empty e)
    (hb : Wf ((X, ⊥) :: Γ) b A e) :
    Eqv Γ A e (.let₁ (.abort a) b) (.let₁ a (.let₁ (.abort (.var 0)) b.wk1)) :=
  .step (.rewrite (.let₁ (.abort ha) hb)
    (.let₁ ha (.let₁ (.abort (wf_var0 Γ empty e)) (wf_wk1 hb empty))) (.let1_abort a b))

theorem source_abortSequence (ha : Wf Γ a empty e) :
    Eqv Γ A e (.abort a) (.let₁ a (.abort (.var 0))) := by
  have h := source_commute_abort ha (wf_var0 Γ A e)
  exact (letEta (.abort ha)).symm.trans
    (h.trans (.let1 (.refl ha) (letEta (.abort (wf_var0 Γ empty e)))))

private theorem source_emptyInitial (ha : Wf Γ a empty e)
    (hb : Wf ((X, ⊥) :: Γ) b A e) (hc : Wf ((Y, ⊥) :: Γ) c A e) :
    Eqv Γ A e (.let₁ (.abort a) b) (.let₁ (.abort a) c) := by
  have hi : InitialContext ((empty, ⊥) :: Γ) := ⟨0, .empty, rfl⟩
  have left := Wf.let₁ (.abort (wf_var0 Γ empty e)) (wf_wk1 hb empty)
  have right := Wf.let₁ (.abort (wf_var0 Γ empty e)) (wf_wk1 hc empty)
  exact (source_commute_abort ha hb).trans
    ((Eqv.let1 (.refl ha) (.step (.initial hi left right))).trans (source_commute_abort ha hc).symm)

private theorem readback_abortSequence {t s : Tm Empty Φ Γ.length}
    (h : AbortSequence (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx t s A)
    (ha : Wf Γ (readback t) A e) (hb : Wf Γ (readback s) A e) :
    Eqv Γ A e (readback t) (readback s) := by
  cases h with
  | sequence _ =>
    cases ha with
    | abort ha => exact source_abortSequence ha
  | unsequence _ =>
    cases hb with
    | abort hb => exact (source_abortSequence hb).symm

theorem abortSequence_reflection (a b : TypedExpr Φ Γ A e)
    {t s : Tm Empty Φ Γ.length} (ha : a.val.toLetIter Γ.length = some t) (hb : b.val.toLetIter Γ.length = some s)
    (h : AbortSequence (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx t s A) : Eqv Γ A e a.val b.val := by
  rw [← readback_lower ha, ← readback_lower hb]
  exact readback_abortSequence h ((readback_lower ha).symm ▸ a.prop) ((readback_lower hb).symm ▸ b.prop)

end SourceRules

variable [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

private theorem wf_readback {t : Tm Empty Φ Γ.length} (hp : Γ.Pure) (hl : LoopFree t)
    (ht : HasTypeEffect (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx t A e) :
    Wf Γ (readback t) A e :=
  Wf.ofLetIter hp (lower_readback hl) ht

private theorem wf_pure_readback {t : Tm Empty Φ Γ.length} (hp : Γ.Pure) (hl : LoopFree t)
    (ht : Wf Γ (readback t) A e) (h : Pure (⊥ : ε) t) :
    Wf Γ (readback t) A (⊥ : ε) := by
  obtain ⟨_, heq, ht⟩ := ht.toLetIter
  have hty := Option.some.inj (heq.symm.trans (lower_readback hl)) ▸ ht.1
  exact wf_readback hp hl ⟨hty, h.hasEffect⟩

private theorem readback_core {t s : Tm Empty Φ Γ.length}
    (hp : Γ.Pure) (h : CoreAxiom (⊥ : ε) t s)
    (lt : LoopFree t) (ls : LoopFree s)
    (ht : HasTypeEffect (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx t A e)
    (hs : HasTypeEffect (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx s A e) :
    Eqv Γ A e (readback t) (readback s) := by
  have ha := wf_readback hp lt ht
  have hb := wf_readback hp ls hs
  cases h with
  | structural h =>
    cases h with
    | letBeta h =>
      rw [readback_instantiate lt.1 lt.2]
      cases ha with
      | let₁ ha hc => exact .step (.let1_beta (wf_pure_readback hp lt.1 ha h) hc)
    | letEta a => exact .step (.rewrite ha hb (.let1_eta _))
    | unitEta a =>
      cases ha with
      | let₁ _ hunit =>
        cases hunit
        exact unitEta hb
    | pairBeta a b c =>
      refine .step (.rewrite ha hb ?_)
      simp only [readback, readback_lift lt.1.2]
      exact .let2_pair (readback a) (readback b) (readback c)
    | pairEta a => exact .step (.rewrite ha hb (.let2_eta _))
    | caseBetaL a l r => exact .step (.reduce ha hb (.case_inl (readback a) (readback l) (readback r)))
    | caseBetaR a l r => exact .step (.reduce ha hb (.case_inr (readback a) (readback l) (readback r)))
    | caseEta a => exact .step (.rewrite ha hb (.case_eta _))
    | emptyInitial a b c =>
      cases ha with
      | let₁ harg hbody =>
        cases harg with
        | abort hpayload =>
          cases hb with
          | let₁ _ hbody' => exact source_emptyInitial hpayload hbody hbody'
  | sequencing h =>
    apply Eqv.step
    refine .rewrite ha hb ?_
    cases h with
    | bindOp a c =>
      simp only [readback, readback_underBinder lt.2]
      exact .let1_op _ (readback a) (readback c)
    | bindLet a b c =>
      simpa only [readback, readback_underBinder lt.2] using Rewrite.let1_let1 (readback a) (readback b) (readback c)
    | bindLetPair a b c =>
      simpa only [readback, readback_underBinder₂ lt.2] using
        Rewrite.let1_let2 (readback a) (readback b) (readback c)
    | bindLetCase a l r c =>
      simpa only [readback, readback_underBinder lt.2] using
        Rewrite.let1_case (readback a) (readback l) (readback r) (readback c)
    | bindPair a b =>
      simp only [readback, readback_underTwoBinders lt.2]
      exact .let2_bind (readback a) (readback b)
    | bindCase a l r =>
      simp only [readback, readback_underBinder lt.2.1, readback_underBinder lt.2.2]
      exact .case_bind (readback a) (readback l) (readback r)
  | iteration h => cases h <;> simp [LoopFree] at lt

private theorem typed_lowering {a : Expr Φ} {t : Tm Empty Φ Γ.length}
    (h : Wf Γ a A e) (ht : a.toLetIter Γ.length = some t) :
    HasTypeEffect (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx t A e := by
  obtain ⟨_, hr, hty⟩ := h.toLetIter
  exact Option.some.inj (hr.symm.trans ht) ▸ hty

theorem core_reflection (hp : Γ.Pure) (a b : TypedExpr Φ Γ A e)
    {t s : Tm Empty Φ Γ.length} (ha : a.val.toLetIter Γ.length = some t) (hb : b.val.toLetIter Γ.length = some s)
    (h : CoreAxiom (⊥ : ε) t s) : Eqv Γ A e a.val b.val := by
  simpa only [readback_lower ha, readback_lower hb] using
    readback_core hp h (loopFree_of_lowering ha) (loopFree_of_lowering hb)
      (typed_lowering a.prop ha) (typed_lowering b.prop hb)

end Silmaril.Isotope.LetIter.PaperExpression.Source.NativeProofs
