module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Defs

/-! # Unary β under product and sum constructors
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.UnaryReturn Paper.RetainedLet

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

inductive Normalizes : VCtx τ → Tm Φ → Tm Φ → τ → Prop where
  | value {Γ : VCtx τ} {c : Tm Φ} {D : τ} (hc : Tm.BranchValue Γ c D) : Normalizes Γ c c D
  | let₁ {Γ : VCtx τ} {a b c d : Tm Φ} {A D : τ}
      (ha : Normalizes Γ a c A) (hb : Normalizes (A :: Γ) b d D) :
      Normalizes Γ (.let₁ a b) (d.subst (Tm.singleSubst c)) D
  | pair {Γ : VCtx τ} {a b c d : Tm Φ} {A B : τ}
      (ha : Normalizes Γ a c A) (hb : Normalizes Γ b d B) :
      Normalizes Γ (.pair a b) (.pair c d) (product A B)
  | inl {Γ : VCtx τ} {a c : Tm Φ} {A B : τ} (ha : Normalizes Γ a c A) :
      Normalizes Γ (.inl a) (.inl c) (coprod A B)
  | inr {Γ : VCtx τ} {a c : Tm Φ} {A B : τ} (ha : Normalizes Γ a c B) :
      Normalizes Γ (.inr a) (.inr c) (coprod A B)

theorem Normalizes.ofBeta {Γ : VCtx τ} {t c : Tm Φ} {D : τ}
    (h : BetaNormalizes Γ t c D) : Normalizes Γ t c D := by
  induction h with
  | value hc => exact .value hc
  | let₁ _ _ ha hb => exact .let₁ ha hb

variable [HasTy Φ τ] {Γ : VCtx τ} {A B D : τ} {t c : Tm Φ}

theorem Normalizes.typed (h : Normalizes Γ t c D) :
    Tm.HasType Γ t D ∧ Tm.BranchValue Γ c D := by
  induction h with
  | value hc => exact ⟨hc.hasType, hc⟩
  | let₁ _ _ ha hb => exact ⟨.let₁ ha.1 hb.1, ha.2.singleSubst hb.2⟩
  | pair _ _ ha hb => exact ⟨.pair ha.1 hb.1, .pair ha.2 hb.2⟩
  | inl _ ha => exact ⟨.inl ha.1, .inl ha.2⟩
  | inr _ ha => exact ⟨.inr ha.1, .inr ha.2⟩

def pairSequence (a b : Tm Φ) : Region Φ :=
  .let₁ a (.let₁ (b.rename Nat.succ) (.br 0 (.pair (.var 1) (.var 0))))

def inlSequence (a : Tm Φ) : Region Φ :=
  .let₁ a (.br 0 (.inl (.var 0)))

def inrSequence (a : Tm Φ) : Region Φ :=
  .let₁ a (.br 0 (.inr (.var 0)))

/-- Sufficient equations for sequencing constructor arguments in the
chosen extension. These are premises on the relation. Pair sequencing
retains the original context for the right operand and evaluates left first. -/
structure ConstructorSequencing (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) : Prop where
  pair {Γ : VCtx τ} {a b c d : Tm Φ} {A B : τ} : Normalizes Γ a c A → Normalizes Γ b d B →
    Paper.Extension.Eqv Seed Γ (returnOnce (.pair a b)) (pairSequence a b) [product A B]
  inl {Γ : VCtx τ} {a c : Tm Φ} {A B : τ} : Normalizes Γ a c A →
    Paper.Extension.Eqv Seed Γ (returnOnce (.inl a)) (inlSequence a) [coprod A B]
  inr {Γ : VCtx τ} {a c : Tm Φ} {A B : τ} : Normalizes Γ a c B →
    Paper.Extension.Eqv Seed Γ (returnOnce (.inr a)) (inrSequence a) [coprod A B]

end Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors
