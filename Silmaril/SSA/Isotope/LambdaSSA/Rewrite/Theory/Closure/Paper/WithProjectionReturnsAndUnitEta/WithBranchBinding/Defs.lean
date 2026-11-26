module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.BranchNormalization.Defs

/-! # Opt-in branch binding in the joined region theory -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Old" => WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)

/-- Bind an arbitrary typed branch argument exactly once before transferring control. -/
inductive BindStep : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | bind {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {a : Tm Φ} {A : τ}
      (hℓ : At L ℓ A) (ha : Tm.HasType Γ a A) :
      BindStep Γ (.br ℓ a) (.let₁ a (.br ℓ (.var 0))) L

/-- Add the typed branch rule to a seed for the Paper contextual closure. -/
abbrev AddBinding (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  Seed Γ r s L ∨ BindStep Γ r s L

/-- Start with the projection-return and unit-η join and add the typed branch rule. -/
abbrev Step := AddBinding (Old)

abbrev Eqv := Extension.Eqv (Step (τ := τ) (Φ := Φ))

def rawSetoid (Γ : VCtx τ) (L : LCtx τ) : Setoid {r : Region Φ // HasType Γ r L} where
  r r s := Eqv Γ r.val s.val L
  iseqv := ⟨fun r => Extension.Eqv.refl r.property, Extension.Eqv.symm, Extension.Eqv.trans⟩

/-- Exactly typed regions modulo the opt-in joined branch-binding relation. -/
abbrev RawRegionClass (Γ : VCtx τ) (L : LCtx τ) := Quotient (rawSetoid (Φ := Φ) Γ L)

variable {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}

def rawClass (hr : HasType Γ r L) : RawRegionClass (Φ := Φ) Γ L := Quotient.mk _ ⟨r, hr⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
