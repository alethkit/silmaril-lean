module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.BranchNormalization.Defs

/-! # Reduction of the raw round trip to the branch equation -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedBranchNormalization

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithProjectionReturnsAndUnitEta (Step)
open Paper.WithProjectionReturnsAndUnitEta.BranchNormalization

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}

local notation "E" => Paper.Extension.Eqv (Step (τ := τ) (Φ := Φ))

theorem bindBranchArguments_eqv_of_br
    (bindBr : ∀ {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {ℓ : Nat} {A : τ},
      At L ℓ A → Tm.HasType Γ a A → E Γ (.let₁ a (.br ℓ (.var 0))) (.br ℓ a) L)
    (hr : HasType Γ r L) : E Γ r.bindBranchArguments r L := by
  induction hr with
  | br hℓ ha => exact bindBr hℓ ha
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb

theorem raw_roundtrip_iff_br :
    (∀ (Γ : VCtx τ) (L : LCtx τ) (q : RawRegionClass (Φ := Φ) Γ L), toRaw (normalize q) = q) ↔
    (∀ {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {ℓ : Nat} {A : τ},
      At L ℓ A → Tm.HasType Γ a A → E Γ (.let₁ a (.br ℓ (.var 0))) (.br ℓ a) L) := by
  constructor
  · intro roundTrip Γ L a ℓ A hℓ ha
    exact Quotient.exact (roundTrip Γ L (rawClass (.br hℓ ha)))
  · intro bindBr Γ L q
    exact Quotient.inductionOn q (fun r =>
      Quotient.sound (bindBranchArguments_eqv_of_br bindBr r.property))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedBranchNormalization
