module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Substitution.Thms
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.NativeProofs

open LocallyNameless (Tm HasType Equiv AbortEquiv Refinement)

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  {pe : ε} {n : Nat} {β : BoundCtx τ n} {A : τ}
  {a b : Expr Φ} {t s : Tm Empty Φ n}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

private theorem one_lt_add_two (n : Nat) : 1 < n + 2 := by omega

/-- The source commuting conversion through abort needs only the existing
abort-sequencing generator followed by exact reassociation. -/
theorem commute_abort {c : Tm Empty Φ (n + 1)} {X : τ}
    (ht : HasType Φ Γ₀ β t empty) (hc : HasType Φ Γ₀ (.snoc β X) c A) :
    AbortEquiv pe Γ₀ β (.let₁ (.abort t) c)
      (.let₁ t (.let₁ (.abort (.bv 0)) c.underBinder)) A :=
  (Refinement.let₁ (AbortEquiv.sequence ht) (Refinement.refl hc)).trans
    (.equiv (Equiv.bindLet ht (.abort .bv) hc))

theorem rewrite_toLetIter (h : Rewrite a b)
    (ha : a.toLetIter n = some t) (hb : b.toLetIter n = some s)
    (ht : HasType Φ Γ₀ β t A) (hs : HasType Φ Γ₀ β s A) :
    AbortEquiv pe Γ₀ β t s A := by
  cases h with
  | let1_op f a b =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨x, ⟨a', ha, rfl⟩, b', hc, rfl⟩ := ha
    simp only [Expr.toLetIter, ha, Expr.toLetIter_wk1 hc, Nat.zero_lt_succ, dite_true,
      Option.bind_some, Option.map_some, Option.some.injEq] at hb
    subst s
    exact .equiv (.ax (.sequencing (.bindOp a' b')) ht hs)
  | let1_let1 a b c =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨x, ⟨a', ha, b', hb', rfl⟩, c', hc, rfl⟩ := ha
    simp only [Expr.toLetIter, ha, hb', Expr.toLetIter_wk1 hc,
      Option.bind_some, Option.map_some, Option.some.injEq] at hb
    subst s
    exact .equiv (.ax (.sequencing (.bindLet a' b' c')) ht hs)
  | let1_let2 a b c =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨x, ⟨a', ha, b', hb', rfl⟩, c', hc, rfl⟩ := ha
    have shifted := Expr.toLetIter_wk1 (Expr.toLetIter_wk1 hc)
    simp only [Expr.toLetIter, ha, hb', shifted,
      Option.bind_some, Option.map_some, Option.some.injEq] at hb
    subst s
    exact .equiv (.ax (.sequencing (.bindLetPair a' b' c')) ht hs)
  | let1_case a l r b =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨x, ⟨a', ha, l', hl, r', hr, rfl⟩, b', hc, rfl⟩ := ha
    simp only [Expr.toLetIter, ha, hl, hr, Expr.toLetIter_wk1 hc,
      Option.bind_some, Option.map_some, Option.some.injEq] at hb
    subst s
    exact .equiv (.ax (.sequencing (.bindLetCase a' l' r' b')) ht hs)
  | let1_abort a b =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨x, ⟨a', ha, rfl⟩, b', hc, rfl⟩ := ha
    simp only [Expr.toLetIter, ha, Expr.toLetIter_wk1 hc, Nat.zero_lt_succ, dite_true,
      Option.bind_some, Option.map_some, Option.some.injEq] at hb
    subst s
    cases ht with
    | let₁ ht hc =>
      cases ht with
      | abort ht => exact commute_abort ht hc
  | let2_eta a =>
    simp only [Expr.toLetIter, one_lt_add_two, Nat.zero_lt_succ, dite_true,
      Option.bind_some, Option.map_some, Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨a', ha, rfl⟩ := ha
    rw [hb] at ha
    cases ha
    exact .equiv (.ax (.structural (.pairEta s)) ht hs)
  | let2_pair a b c =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨x, ⟨a', ha, b', hb', rfl⟩, c', hc, rfl⟩ := ha
    simp only [Expr.toLetIter, ha, Expr.toLetIter_wk0 hb', hc,
      Option.bind_some, Option.map_some, Option.some.injEq] at hb
    subst s
    exact .equiv (.ax (.structural (.pairBeta a' b' c')) ht hs)
  | let1_eta a =>
    simp only [Expr.toLetIter, Nat.zero_lt_succ, dite_true, Option.map_some,
      Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨a', ha, rfl⟩ := ha
    rw [hb] at ha
    cases ha
    exact .equiv (.ax (.structural (.letEta s)) ht hs)
  | let2_bind a b =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨a', ha, b', hc, rfl⟩ := ha
    simp only [Expr.toLetIter, ha, Expr.toLetIter_wk2 hc, Nat.zero_lt_succ, dite_true,
      Option.bind_some, Option.map_some, Option.some.injEq] at hb
    subst s
    exact .equiv (.ax (.sequencing (.bindPair a' b')) ht hs)
  | case_bind a l r =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨a', ha, l', hl, r', hr, rfl⟩ := ha
    simp only [Expr.toLetIter, ha, Expr.toLetIter_wk1 hl, Expr.toLetIter_wk1 hr, Nat.zero_lt_succ, dite_true,
      Option.bind_some, Option.map_some, Option.some.injEq] at hb
    subst s
    exact .equiv (.ax (.sequencing (.bindCase a' l' r')) ht hs)
  | case_eta a =>
    simp only [Expr.toLetIter, Nat.zero_lt_succ, dite_true, Option.bind_some, Option.map_some,
      Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨a', ha, rfl⟩ := ha
    rw [hb] at ha
    cases ha
    exact .equiv (.ax (.structural (.caseEta s)) ht hs)

theorem reduce_toLetIter (h : Reduce a b)
    (ha : a.toLetIter n = some t) (hb : b.toLetIter n = some s)
    (ht : HasType Φ Γ₀ β t A) (hs : HasType Φ Γ₀ β s A) :
    Equiv pe Γ₀ β t s A := by
  cases h with
  | case_inl a l r =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨x, ⟨a', ha, rfl⟩, l', hl, r', hr, rfl⟩ := ha
    simp only [Expr.toLetIter, ha, hl, Option.bind_some, Option.map_some, Option.some.injEq] at hb
    subst s
    exact .ax (.structural (.caseBetaL a' l' r')) ht hs
  | case_inr a l r =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    obtain ⟨x, ⟨a', ha, rfl⟩, l', hl, r', hr, rfl⟩ := ha
    simp only [Expr.toLetIter, ha, hr, Option.bind_some, Option.map_some, Option.some.injEq] at hb
    subst s
    exact .ax (.structural (.caseBetaR a' l' r')) ht hs

end Silmaril.Isotope.LetIter.PaperExpression.Source.NativeProofs
