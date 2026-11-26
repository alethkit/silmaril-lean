module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Defs

/-! # Opt-in sequencing of a returned primitive call -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns

open CfgEta.TypeCategory (returnRegion returnRegion_typed)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Evaluate the operand once before the primitive consumes the bound value.
The equation is restricted to returning the call result at one exit. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | seq {Γ : VCtx τ} {a : Tm Φ} (p : Φ) (ha : Tm.HasType Γ a (instrSrc p)) :
      Step Γ (returnRegion (.op p a)) (returnRegion (.let₁ a (.op p (.var 0)))) [instrTrg p]

/-- The ordinary lowering of each endpoint already uses constructor-valued branches. -/
theorem Step.valueBranches {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ} (h : Step Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases h with
  | seq p ha => exact ⟨returnRegion_typed (.op ha), returnRegion_typed (.let₁ ha (.op (.var (i := 0) rfl)))⟩

variable {ε : Type w} [HasEff Φ ε]

/-- Extend the existing ordered-pair join by the single computed-call equation. -/
abbrev JoinedStep (pe : ε) (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithPairReturns.JoinedStep pe Γ r s L ∨ Step Γ r s L

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns
