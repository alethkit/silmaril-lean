module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CaseModel

/-! # Native iteration and coproduct application reductions -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem Equates.iter {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a a' : Term Φ n} {b b' : Term Φ (n + 1)} {A B : τ}
    (cap : F.HasIter) (split : Γ.Split Γl Γr) (hu : Γl.linearity = ⊤)
    (ha : Equates (ε := ε) F R Γr a a' A)
    (hb : Equates (ε := ε) F R (Γl.snoc A) b b' (coprod B A)) :
    Equates (ε := ε) F R Γ (.iter a b) (.iter a' b') B :=
  ⟨.iter cap split hu ha.1 hb.1, .iter cap split hu ha.2 hb.2⟩

namespace Models.Syntactic

theorem iter_hasCase (cap : F.HasIter) : F.HasCase := by cases F <;> trivial

theorem atIndex_iterateTerm {n : Nat} (i : Fin n) (f : Term Φ 1) :
    atIndex i (iterateTerm f) = .iter (.bv i) (atIndex 0 f) := by
  simp only [atIndex, iterateTerm, continuation, Tm.rename, Tm.rename_comp]
  congr 1
  apply Tm.rename_congr
  intro j
  have hj : j = 0 := Fin.eq_zero j
  subst j
  rfl

theorem action_desc {n : Nat} {Γ : QCtx τ n} {a : Term Φ n}
    {f g : Term Φ 1} {A B C : τ} (cap : F.HasCase)
    (ha : HasType F Γ (⊤ : ε) a (coprod A B))
    (hf : HasType F (input A) (⊤ : ε) f C)
    (hg : HasType F (input B) (⊤ : ε) g C) :
    Equates (ε := ε) F R Γ (action a (descTerm f g))
      (.case a (atIndex 0 f) (atIndex 0 g)) C := by
  have h := case_bind (R := R) cap (QCtx.Split.zero_left Γ) ha
    (atZeroDeriv Γ hf) (atZeroDeriv Γ hg)
  simpa only [action, caseContinuation, atIndex_descTerm, underBinder_atIndex_zero] using h.symm

theorem action_iterate {n : Nat} {Γ : QCtx τ n} {a : Term Φ n}
    {f : Term Φ 1} {A B : τ} (cap : F.HasIter)
    (ha : HasType F Γ (⊤ : ε) a A)
    (hf : HasType F (input A) (⊤ : ε) f (coprod B A)) :
    Equates (ε := ε) F R Γ (action a (iterateTerm f)) (.iter a (atIndex 0 f)) B := by
  have hl := actionDeriv ha (iterateDeriv cap EffectSystem.iterable_top hf)
  have hr := HasType.iter cap (QCtx.Split.zero_left Γ) Γ.zero_linearity
    EffectSystem.iterable_top ha (atZeroDeriv Γ hf)
  have h := Equates.ofAxiom (R := R)
    (.iterBind cap (QCtx.Split.zero_left Γ) Γ.zero_linearity EffectSystem.iterable_top
      ha (atZeroDeriv Γ hf)) ⟨hr⟩
    (by simpa only [action, atIndex_iterateTerm, underBinder_atIndex_zero] using
      (show WellTyped (ε := ε) F Γ (action a (iterateTerm f)) B from ⟨hl⟩))
  simpa only [action, atIndex_iterateTerm, underBinder_atIndex_zero] using h.symm

/-- A single use under a pure injection satisfies both directed beta rules. -/
theorem action_inl {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A B : τ}
    (cap : F.HasCase) (ha : HasType F Γ (⊤ : ε) a A) :
    Equates (ε := ε) F R Γ (action a (.inl (.bv 0))) (.inl a) (coprod A B) := by
  exact linearBeta (QCtx.Split.zero_right Γ) ha
    (.inl cap (zeroParameter Γ A (.used .linear) (⊥ : ε) le_rfl))
    (atZeroDeriv Γ (inlDeriv cap A B (⊥ : ε)))
    (EffectSystem.pure_commutes (⊤ : ε)).symm ⟨.inl cap ha⟩

theorem action_inr {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A B : τ}
    (cap : F.HasCase) (ha : HasType F Γ (⊤ : ε) a B) :
    Equates (ε := ε) F R Γ (action a (.inr (.bv 0))) (.inr a) (coprod A B) := by
  exact linearBeta (QCtx.Split.zero_right Γ) ha
    (.inr cap (zeroParameter Γ B (.used .linear) (⊥ : ε) le_rfl))
    (atZeroDeriv Γ (inrDeriv cap A B (⊥ : ε)))
    (EffectSystem.pure_commutes (⊤ : ε)).symm ⟨.inr cap ha⟩

end Models.Syntactic
end Silmaril.Isotope.Refinement
