module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CaseContexts

/-! # Coproduct arrows acting in arbitrary quantitative contexts -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem atIndex_descTerm {n : Nat} (i : Fin n) (f g : Term Φ 1) :
    atIndex i (descTerm f g) = .case (.bv i) (atIndex 0 f) (atIndex 0 g) := by
  simp only [atIndex, descTerm, continuation, Tm.rename, Tm.rename_comp]
  congr 2 <;> funext j <;>
    have hj : j = 0 := Fin.eq_zero j <;> subst j <;> rfl

theorem action_inl_desc {n : Nat} {Γ : QCtx τ n} {a : Term Φ n}
    {f g : Term Φ 1} {A B C : τ} (cap : F.HasCase)
    (ha : HasType F Γ (⊤ : ε) a A)
    (hf : HasType F (input A) (⊤ : ε) f C) (hg : HasType F (input B) (⊤ : ε) g C) :
    Equates (ε := ε) F R Γ (action (.inl a) (descTerm f g)) (action a f) C := by
  have hb := case_bind (R := R) cap (QCtx.Split.zero_left Γ) (HasType.inl cap ha)
    (atZeroDeriv Γ hf) (atZeroDeriv Γ hg)
  have hβ := Equates.ofAxiom (R := R)
    (.caseBetaL cap (QCtx.Split.zero_left Γ) ha (atZeroDeriv Γ hf) (atZeroDeriv Γ hg))
    ⟨.case cap (QCtx.Split.zero_left Γ) (.inl cap ha) (atZeroDeriv Γ hf) (atZeroDeriv Γ hg)⟩
    ⟨actionDeriv ha hf⟩
  have h := hb.symm.trans hβ
  simpa only [action, caseContinuation, atIndex_descTerm, underBinder_atIndex_zero] using h

theorem action_inr_desc {n : Nat} {Γ : QCtx τ n} {a : Term Φ n}
    {f g : Term Φ 1} {A B C : τ} (cap : F.HasCase)
    (ha : HasType F Γ (⊤ : ε) a B)
    (hf : HasType F (input A) (⊤ : ε) f C) (hg : HasType F (input B) (⊤ : ε) g C) :
    Equates (ε := ε) F R Γ (action (.inr a) (descTerm f g)) (action a g) C := by
  have hb := case_bind (R := R) cap (QCtx.Split.zero_left Γ) (HasType.inr cap ha)
    (atZeroDeriv Γ hf) (atZeroDeriv Γ hg)
  have hβ := Equates.ofAxiom (R := R)
    (.caseBetaR cap (QCtx.Split.zero_left Γ) ha (atZeroDeriv Γ hf) (atZeroDeriv Γ hg))
    ⟨.case cap (QCtx.Split.zero_left Γ) (.inr cap ha) (atZeroDeriv Γ hf) (atZeroDeriv Γ hg)⟩
    ⟨actionDeriv ha hg⟩
  have h := hb.symm.trans hβ
  simpa only [action, caseContinuation, atIndex_descTerm, underBinder_atIndex_zero] using h

theorem pure_action_inl {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A B : τ}
    (cap : F.HasCase) (ha : HasType F Γ (⊥ : ε) a A) (hq : quantity A ≤ Γ.linearity) :
    Equates (ε := ε) F R Γ (action a (.inl (.bv 0))) (.inl a) (coprod A B) :=
  pureBetaTyped (QCtx.Split.zero_right Γ) ha (atZeroDeriv Γ (inlDeriv cap A B (⊤ : ε))) hq

theorem pure_action_inr {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A B : τ}
    (cap : F.HasCase) (ha : HasType F Γ (⊥ : ε) a B) (hq : quantity B ≤ Γ.linearity) :
    Equates (ε := ε) F R Γ (action a (.inr (.bv 0))) (.inr a) (coprod A B) :=
  pureBetaTyped (QCtx.Split.zero_right Γ) ha (atZeroDeriv Γ (inrDeriv cap A B (⊤ : ε))) hq

end Silmaril.Isotope.Refinement.Models.Syntactic
