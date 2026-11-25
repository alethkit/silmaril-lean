module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Defs

/-! # Source renaming and substitution at annotated contexts -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs

open Expr

variable {τ : Type u} {Φ : Type v} {ε : Type w}

private theorem liftWk_comp (ρ ξ : Nat → Nat) :
    liftWk (ρ ∘ ξ) = liftWk ρ ∘ liftWk ξ := by
  funext i
  cases i <;> rfl

theorem wk_wk (a : Expr Φ) (ρ ξ : Nat → Nat) :
    (a.wk ξ).wk ρ = a.wk (ρ ∘ ξ) := by
  induction a generalizing ρ ξ <;> simp only [wk, liftWk_comp, Function.comp_apply, *]

private theorem liftSubst_comp_wk (σ : Nat → Expr Φ) (ρ : Nat → Nat) :
    liftSubst (σ ∘ ρ) = liftSubst σ ∘ liftWk ρ := by
  funext i
  cases i <;> rfl

theorem subst_wk (a : Expr Φ) (σ : Nat → Expr Φ) (ρ : Nat → Nat) :
    (a.wk ρ).subst σ = a.subst (σ ∘ ρ) := by
  induction a generalizing σ ρ <;> simp only [wk, subst, liftSubst_comp_wk, Function.comp_apply, *]

private theorem wk_liftSubst (σ : Nat → Expr Φ) (ρ : Nat → Nat) :
    liftSubst (fun i => (σ i).wk ρ) = fun i => ((liftSubst σ) i).wk (liftWk ρ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp only [liftSubst, wk0, wk_wk]; rfl

theorem wk_subst (a : Expr Φ) (σ : Nat → Expr Φ) (ρ : Nat → Nat) :
    (a.subst σ).wk ρ = a.subst (fun i => (σ i).wk ρ) := by
  induction a generalizing σ ρ <;> simp only [wk, subst, wk_liftSubst, *]

private theorem liftSubst_comp_subst (σ θ : Nat → Expr Φ) :
    liftSubst (fun i => (θ i).subst σ) = fun i => ((liftSubst θ) i).subst (liftSubst σ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp only [liftSubst, wk0, subst_wk, wk_subst]; rfl

theorem subst_subst (a : Expr Φ) (σ θ : Nat → Expr Φ) :
    (a.subst θ).subst σ = a.subst (fun i => (θ i).subst σ) := by
  induction a generalizing σ θ <;> simp only [subst, liftSubst_comp_subst, *]

private theorem liftSubst_var : liftSubst (Expr.var : Nat → Expr Φ) = Expr.var := by
  funext i
  cases i <;> rfl

@[simp] theorem subst_var (a : Expr Φ) : a.subst Expr.var = a := by
  induction a <;> simp only [subst, liftSubst_var, *]

theorem subst0_wk0 (a b : Expr Φ) : b.wk0.subst a.subst0 = b := by
  rw [wk0, subst_wk]
  exact subst_var b

theorem subst0_subst (a b : Expr Φ) (σ : Nat → Expr Φ) :
    (b.subst a.subst0).subst σ = (b.subst (liftSubst σ)).subst (a.subst σ).subst0 := by
  rw [subst_subst, subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact (subst0_wk0 _ _).symm

theorem wk1_subst_lift (b : Expr Φ) (σ : Nat → Expr Φ) :
    b.wk1.subst (liftSubst (liftSubst σ)) = (b.subst (liftSubst σ)).wk1 := by
  simp only [wk1, subst_wk, wk_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => simp only [Function.comp_apply, liftWk, liftSubst, wk0, wk_wk]; rfl

theorem wk2_subst_lift (b : Expr Φ) (σ : Nat → Expr Φ) :
    b.wk2.subst (liftSubst (liftSubst (liftSubst σ))) =
      (b.subst (liftSubst (liftSubst σ))).wk2 := by
  simp only [wk2, subst_wk, wk_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i => simp only [Function.comp_apply, liftWk, liftSubst, wk0, wk_wk]; rfl

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [Bot ε]

theorem wf_wkEff {Γ : EffectCtx τ ε} {a : Expr Φ} {A : τ} {e hi : ε}
    (d : Wf Γ a A e) (h : e ≤ hi) : Wf Γ a A hi := by
  induction d generalizing hi with
  | var i he => exact .var i (he.trans h)
  | op hf _ ih => exact .op (hf.trans h) (ih h)
  | unit Γ _ => exact .unit Γ hi
  | _ => constructor <;> solve_by_elim

/-- A renaming locates every old slot at the same type and no larger effect. -/
def Renaming (Γ Δ : EffectCtx τ ε) (ρ : Nat → Nat) : Prop :=
  ∀ i : Fin Δ.length, ∃ j : Fin Γ.length,
    ρ i.val = j.val ∧ (Γ.get j).1 = (Δ.get i).1 ∧ (Γ.get j).2 ≤ (Δ.get i).2

omit [TypeFormers τ] [Bot ε] in
theorem Renaming.lift {Γ Δ : EffectCtx τ ε} {ρ : Nat → Nat}
    (h : Renaming Γ Δ ρ) (slot : τ × ε) :
    Renaming (slot :: Γ) (slot :: Δ) (liftWk ρ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨0, rfl, rfl, le_rfl⟩
  · obtain ⟨k, hk, ht, he⟩ := h j
    exact ⟨k.succ, congrArg Nat.succ hk, ht, he⟩

omit [TypeFormers τ] [Bot ε] in
theorem Renaming.wk0 (Γ : EffectCtx τ ε) (slot : τ × ε) :
    Renaming (slot :: Γ) Γ Nat.succ :=
  fun i => ⟨i.succ, rfl, rfl, le_rfl⟩

theorem wf_wk {Γ Δ : EffectCtx τ ε} {ρ : Nat → Nat} {a : Expr Φ} {A : τ} {e : ε}
    (d : Wf Δ a A e) (h : Renaming Γ Δ ρ) : Wf Γ (a.wk ρ) A e := by
  induction d generalizing Γ ρ with
  | var i he =>
    obtain ⟨j, hj, ht, he'⟩ := h i
    simpa only [wk, hj, ht] using Wf.var j (he'.trans he)
  | op hf _ ih => exact .op hf (ih h)
  | let₁ _ _ ihA ihB => exact .let₁ (ihA h) (ihB (h.lift _))
  | pair _ _ ihA ihB => exact .pair (ihA h) (ihB h)
  | unit _ e => exact .unit Γ e
  | let₂ _ _ ihA ihB => exact .let₂ (ihA h) (ihB ((h.lift _).lift _))
  | inl _ ih => exact .inl (ih h)
  | inr _ ih => exact .inr (ih h)
  | case _ _ _ ihA ihL ihR => exact .case (ihA h) (ihL (h.lift _)) (ihR (h.lift _))
  | abort _ ih => exact .abort (ih h)

/-- A substitution supplies each slot at its declared type and effect. -/
def TypedSubst (Γ Δ : EffectCtx τ ε) (σ : Nat → Expr Φ) : Prop :=
  ∀ i : Fin Δ.length, Wf Γ (σ i.val) (Δ.get i).1 (Δ.get i).2

theorem TypedSubst.lift {Γ Δ : EffectCtx τ ε} {σ : Nat → Expr Φ}
    (h : TypedSubst Γ Δ σ) (slot : τ × ε) :
    TypedSubst (slot :: Γ) (slot :: Δ) (liftSubst σ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Wf.var 0 le_rfl
  · exact wf_wk (h j) (Renaming.wk0 Γ slot)

theorem TypedSubst.subst0 {Γ : EffectCtx τ ε} {a : Expr Φ} {A : τ} {e : ε}
    (h : Wf Γ a A e) : TypedSubst Γ ((A, e) :: Γ) a.subst0 := by
  intro i
  refine Fin.cases h (fun j => ?_) i
  exact Wf.var j le_rfl

theorem wf_subst {Γ Δ : EffectCtx τ ε} {σ : Nat → Expr Φ}
    {a : Expr Φ} {A : τ} {e : ε} (d : Wf Δ a A e)
    (h : TypedSubst Γ Δ σ) : Wf Γ (a.subst σ) A e := by
  induction d generalizing Γ σ with
  | var i he => exact wf_wkEff (h i) he
  | op hf _ ih => exact .op hf (ih h)
  | let₁ _ _ ihA ihB => exact .let₁ (ihA h) (ihB (h.lift _))
  | pair _ _ ihA ihB => exact .pair (ihA h) (ihB h)
  | unit _ e => exact .unit Γ e
  | let₂ _ _ ihA ihB => exact .let₂ (ihA h) (ihB ((h.lift _).lift _))
  | inl _ ih => exact .inl (ih h)
  | inr _ ih => exact .inr (ih h)
  | case _ _ _ ihA ihL ihR => exact .case (ihA h) (ihL (h.lift _)) (ihR (h.lift _))
  | abort _ ih => exact .abort (ih h)

end Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs
