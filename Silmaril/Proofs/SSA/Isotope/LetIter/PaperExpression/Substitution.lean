module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Substitution.Defs

set_option backward.isDefEq.respectTransparency false

universe v

namespace Silmaril.Isotope.LetIter.PaperExpression.Expr.Proofs

open LocallyNameless (Tm)

variable {Φ : Type v} {n m : Nat}

private theorem liftWk_agrees {ρ : Nat → Nat} {ξ : Fin n → Fin m}
    (agrees : ∀ i : Fin n, ρ i.val = (ξ i).val) (i : Fin (n + 1)) :
    liftWk ρ i.val = (Tm.up ξ i).val := by
  refine Fin.cases rfl (fun j => ?_) i
  exact congrArg Nat.succ (agrees j)

/-- Lowering commutes with a renaming when it agrees with a finite renaming
on all indices of the source scope. -/
public theorem toLetIter_wk {a : Expr Φ} {t : Tm Empty Φ n}
    {ρ : Nat → Nat} {ξ : Fin n → Fin m}
    (lowered : a.toLetIter n = some t) (agrees : ∀ i : Fin n, ρ i.val = (ξ i).val) :
    (a.wk ρ).toLetIter m = some (t.rename ξ) := by
  induction a generalizing n m ρ with
  | var i =>
    by_cases hi : i < n
    · rw [toLetIter, dite_eq_left hi] at lowered
      obtain rfl := Option.some.inj lowered
      have hr := agrees ⟨i, hi⟩
      change ρ i = (ξ ⟨i, hi⟩).val at hr
      simp [wk, toLetIter, Tm.rename, hr]
    · simp [toLetIter, hi] at lowered
  | op f a ih =>
    simp only [toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    simp [wk, toLetIter, Tm.rename, ih loweredArg agrees]
  | let₁ a b iha ihb =>
    simp only [toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, body, loweredBody, rfl⟩ := lowered
    simp [wk, toLetIter, Tm.rename, iha loweredArg agrees,
      ihb loweredBody (liftWk_agrees agrees)]
  | pair a b iha ihb =>
    simp only [toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨l, loweredL, r, loweredR, rfl⟩ := lowered
    simp [wk, toLetIter, Tm.rename, iha loweredL agrees, ihb loweredR agrees]
  | unit =>
    rw [toLetIter] at lowered
    obtain rfl := Option.some.inj lowered
    rfl
  | let₂ a b iha ihb =>
    simp only [toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, body, loweredBody, rfl⟩ := lowered
    simp [wk, toLetIter, Tm.rename, iha loweredArg agrees,
      ihb loweredBody (liftWk_agrees (liftWk_agrees agrees))]
  | inl a ih =>
    simp only [toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    simp [wk, toLetIter, Tm.rename, ih loweredArg agrees]
  | inr a ih =>
    simp only [toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    simp [wk, toLetIter, Tm.rename, ih loweredArg agrees]
  | case a l r iha ihl ihr =>
    simp only [toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, left, loweredLeft, right, loweredRight, rfl⟩ := lowered
    simp [wk, toLetIter, Tm.rename, iha loweredArg agrees,
      ihl loweredLeft (liftWk_agrees agrees), ihr loweredRight (liftWk_agrees agrees)]
  | abort a ih =>
    simp only [toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    simp [wk, toLetIter, Tm.rename, ih loweredArg agrees]

public theorem toLetIter_wk0 {a : Expr Φ} {t : Tm Empty Φ n} (lowered : a.toLetIter n = some t) :
    a.wk0.toLetIter (n + 1) = some t.lift :=
  toLetIter_wk lowered (ξ := Fin.succ) (fun _ => rfl)

public theorem toLetIter_wk1 {a : Expr Φ} {t : Tm Empty Φ (n + 1)}
    (lowered : a.toLetIter (n + 1) = some t) :
    a.wk1.toLetIter (n + 2) = some t.underBinder :=
  toLetIter_wk lowered (liftWk_agrees (ξ := Fin.succ) (fun _ => rfl))

public theorem toLetIter_wk2 {a : Expr Φ} {t : Tm Empty Φ (n + 2)}
    (lowered : a.toLetIter (n + 2) = some t) :
    a.wk2.toLetIter (n + 3) = some t.underTwoBinders := by
  have hRenaming :
      Tm.up (Tm.up (Fin.succ : Fin n → Fin (n + 1))) =
        Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ)) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun _ => rfl) j
  rw [Tm.underTwoBinders, ← hRenaming]
  exact toLetIter_wk lowered (liftWk_agrees (liftWk_agrees (ξ := Fin.succ) (fun _ => rfl)))

private theorem liftSubst_agrees {σ : Nat → Expr Φ} {θ : Fin n → Tm Empty Φ m}
    (agrees : ∀ i : Fin n, (σ i.val).toLetIter m = some (θ i)) (i : Fin (n + 1)) :
    (liftSubst σ i.val).toLetIter (m + 1) = some (Tm.upSub θ i) := by
  refine Fin.cases rfl (fun j => ?_) i
  exact toLetIter_wk0 (agrees j)

/-- Lowering commutes with a substitution whose images lower to the given
native substitution on all indices of the source scope. -/
public theorem toLetIter_subst {a : Expr Φ} {t : Tm Empty Φ n}
    {σ : Nat → Expr Φ} {θ : Fin n → Tm Empty Φ m}
    (lowered : a.toLetIter n = some t)
    (agrees : ∀ i : Fin n, (σ i.val).toLetIter m = some (θ i)) :
    (a.subst σ).toLetIter m = some (t.bsubst θ) := by
  induction a generalizing n m σ with
  | var i =>
    by_cases hi : i < n
    · rw [toLetIter, dite_eq_left hi] at lowered
      obtain rfl := Option.some.inj lowered
      exact agrees ⟨i, hi⟩
    · simp [toLetIter, hi] at lowered
  | op f a ih =>
    simp only [toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    simp [subst, toLetIter, Tm.bsubst, ih loweredArg agrees]
  | let₁ a b iha ihb =>
    simp only [toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, body, loweredBody, rfl⟩ := lowered
    simp [subst, toLetIter, Tm.bsubst, iha loweredArg agrees,
      ihb loweredBody (liftSubst_agrees agrees)]
  | pair a b iha ihb =>
    simp only [toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨l, loweredL, r, loweredR, rfl⟩ := lowered
    simp [subst, toLetIter, Tm.bsubst, iha loweredL agrees, ihb loweredR agrees]
  | unit =>
    rw [toLetIter] at lowered
    obtain rfl := Option.some.inj lowered
    rfl
  | let₂ a b iha ihb =>
    simp only [toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, body, loweredBody, rfl⟩ := lowered
    simp [subst, toLetIter, Tm.bsubst, iha loweredArg agrees,
      ihb loweredBody (liftSubst_agrees (liftSubst_agrees agrees))]
  | inl a ih =>
    simp only [toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    simp [subst, toLetIter, Tm.bsubst, ih loweredArg agrees]
  | inr a ih =>
    simp only [toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    simp [subst, toLetIter, Tm.bsubst, ih loweredArg agrees]
  | case a l r iha ihl ihr =>
    simp only [toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, left, loweredLeft, right, loweredRight, rfl⟩ := lowered
    simp [subst, toLetIter, Tm.bsubst, iha loweredArg agrees,
      ihl loweredLeft (liftSubst_agrees agrees), ihr loweredRight (liftSubst_agrees agrees)]
  | abort a ih =>
    simp only [toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    simp [subst, toLetIter, Tm.bsubst, ih loweredArg agrees]

/-- The source beta substitution lowers to native instantiation. -/
public theorem toLetIter_subst0 {a b : Expr Φ} {t : Tm Empty Φ n} {s : Tm Empty Φ (n + 1)}
    (loweredArg : a.toLetIter n = some t) (loweredBody : b.toLetIter (n + 1) = some s) :
    (b.subst a.subst0).toLetIter n = some (s.instantiate t) := by
  apply toLetIter_subst loweredBody
  intro i
  refine Fin.cases loweredArg (fun j => ?_) i
  simp [subst0, toLetIter, Fin.cases_succ, j.isLt]

end Silmaril.Isotope.LetIter.PaperExpression.Expr.Proofs
