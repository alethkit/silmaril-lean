module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Thms

/-! # Unary β to constructor values

This fragment has constructor-valued leaves and unary expression lets.
Both the bound expression and the body may contain more unary lets.
The β step substitutes the normalized bound value into the normalized body.

Compare the bottom-effect hypothesis of the companion's
[`Term.Eqv.let1_beta_pure`](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Term/Eqv.lean#L1148-L1149).
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

/-- Normalize a typed unary-let tree to a single constructor value. -/
inductive BetaNormalizes : VCtx τ → Tm Φ → Tm Φ → τ → Prop where
  | value {Γ : VCtx τ} {c : Tm Φ} {D : τ} (hc : Tm.BranchValue Γ c D) :
      BetaNormalizes Γ c c D
  | let₁ {Γ : VCtx τ} {a b c d : Tm Φ} {A D : τ}
      (ha : BetaNormalizes Γ a c A) (hb : BetaNormalizes (A :: Γ) b d D) :
      BetaNormalizes Γ (.let₁ a b) (d.subst (Tm.singleSubst c)) D

variable {Γ : VCtx τ} {a c : Tm Φ} {D : τ}

theorem BetaNormalizes.hasType [HasTy Φ τ] (h : BetaNormalizes Γ a c D) :
    Tm.HasType Γ a D := by
  induction h with
  | value hc => exact hc.hasType
  | let₁ _ _ ha hb => exact .let₁ ha hb

theorem BetaNormalizes.branchValue (h : BetaNormalizes Γ a c D) :
    Tm.BranchValue Γ c D := by
  induction h with
  | value hc => exact hc
  | let₁ _ _ ha hb => exact ha.singleSubst hb

end Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn
