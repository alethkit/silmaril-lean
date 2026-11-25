module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.AssociatorInverses

/-! # Applying syntactic arrows to resource-indexed computations -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Application of a single-input arrow in any quantitative context. -/
def action {n : Nat} (a : Term Φ n) (f : Term Φ 1) : Term Φ n :=
  .let₁ a (atIndex 0 f)

def actionDeriv {n : Nat} {Γ : QCtx τ n} {e : ε} {a : Term Φ n}
    {f : Term Φ 1} {A B : τ} (ha : HasType F Γ e a A)
    (hf : HasType F (input A) e f B) : HasType F Γ e (action a f) B :=
  .let₁ (QCtx.Split.zero_left Γ) ha (atZeroDeriv Γ hf)

theorem action_congr {n : Nat} {Γ : QCtx τ n} {a b : Term Φ n}
    {f : Term Φ 1} {A B : τ} (h : Equates (ε := ε) F R Γ a b A)
    (hf : HasType F (input A) (⊤ : ε) f B) :
    Equates (ε := ε) F R Γ (action a f) (action b f) B :=
  Equates.let₁ (QCtx.Split.zero_left Γ) h (Equates.refl ⟨atZeroDeriv Γ hf⟩)

/-- Acting by a composite is sequential action, from native let reassociation. -/
theorem action_compose {n : Nat} {Γ : QCtx τ n} {a : Term Φ n}
    {f g : Term Φ 1} {A B C : τ} (ha : HasType F Γ (⊤ : ε) a A)
    (hf : HasType F (input A) (⊤ : ε) f B) (hg : HasType F (input B) (⊤ : ε) g C) :
    Equates (ε := ε) F R Γ (action a (composeTerm f g)) (action (action a f) g) C := by
  have h := Equates.ofAxiom (R := R)
    (.letLet (QCtx.Split.zero_left Γ) (QCtx.Split.zero_left Γ.zero) ha
      (atZeroDeriv Γ hf) (atZeroDeriv Γ.zero hg))
    ⟨actionDeriv (actionDeriv ha hf) hg⟩
    (by simpa only [action, atIndex_compose, underBinder_atIndex_zero] using
      (show WellTyped (ε := ε) F Γ (action a (composeTerm f g)) C from
        ⟨actionDeriv ha (composeDeriv hf hg)⟩))
  simpa only [action, atIndex_compose, underBinder_atIndex_zero] using h.symm

/-- Acting after a product elimination acts on its continuation. -/
theorem action_let₂ {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {b : Term Φ (n + 2)} {f : Term Φ 1} {A B C D : τ}
    (split : Γ.Split Γl Γr) (ha : HasType F Γr (⊤ : ε) a (product A B))
    (hb : HasType F ((Γl.snoc A).snoc B) (⊤ : ε) b C)
    (hf : HasType F (input C) (⊤ : ε) f D) :
    Equates (ε := ε) F R Γ (action (.let₂ a b) f) (.let₂ a (action b f)) D := by
  have h := let_pair (R := R) split (QCtx.Split.zero_left Γl) ha hb (atZeroDeriv Γl hf)
  simpa only [action, underBinder_atIndex_zero] using h

/-- Arrows from a product are determined by their action on the two fresh components.
This is extensionality derived from product eta, rather than an extra quotient equation. -/
theorem pair_ext {A B C : τ} {f g : Term Φ 1}
    (hf : HasType F (input (product A B)) (⊤ : ε) f C)
    (hg : HasType F (input (product A B)) (⊤ : ε) g C)
    (h : Equates (ε := ε) F R (pairContext (product A B) A B)
      (action (.pair (.bv 1) (.bv 0)) f) (action (.pair (.bv 1) (.bv 0)) g) C) :
    Equates (ε := ε) F R (input (product A B)) f g C := by
  let P := product A B
  have hp : (QCtx.nil.snoc P .zero).Discardable := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact le_rfl
  have dp := parametersDeriv (F := F) (Φ := Φ) (QCtx.nil.snoc P .zero) hp A B (⊤ : ε)
  have heta := Equates.ofAxiom (R := R) (.pairEta (identityDeriv P (⊤ : ε)))
    ⟨.let₂ (inputSplit P) (identityDeriv P (⊤ : ε)) dp⟩ ⟨identityDeriv P (⊤ : ε)⟩
  have hnormalize (k : Term Φ 1) (hk : HasType F (input P) (⊤ : ε) k C) :
      Equates (ε := ε) F R (input P) k
        (.let₂ (.bv 0) (action (.pair (.bv 1) (.bv 0)) k)) C := by
    have h₀ := identity_compose_equates R (⟨k, ⟨hk⟩⟩ : Arrow (ε := ε) F P C)
    have h₁ := action_congr heta.symm hk
    have h₂ := action_let₂ (R := R) (inputSplit P) (identityDeriv P (⊤ : ε)) dp hk
    apply Equates.trans _ (h₁.trans h₂)
    simpa only [composeArrow, composeTerm, continuation_atIndex, identityArrow, action] using h₀.symm
  exact (hnormalize f hf).trans
    ((Equates.let₂ (inputSplit P) (Equates.refl ⟨identityDeriv P (⊤ : ε)⟩) h).trans
      (hnormalize g hg).symm)

end Silmaril.Isotope.Refinement.Models.Syntactic
