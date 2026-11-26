module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Defs

/-! # The opt-in raw relation reduces to the joined relation on normalized forms -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedBranchBinding

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Old" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
local notation "JoinedEqv" => Paper.Extension.Eqv Old

variable {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

variable {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

theorem ofSeed (h : Paper.Extension.Eqv Seed Γ r s L) :
    Paper.Extension.Eqv (AddBinding Seed) Γ r s L := by
  induction h with
  | paper h => exact .paper h
  | extra hr hs h => exact .extra hr hs (.inl h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | lsubstCongr hp _ ih => exact .lsubstCongr hp ih
  | lsubstPost _ hr hs hσ ih => exact .lsubstPost ih hr hs hσ
  | substVars _ hθ ih => exact .substVars ih hθ
  | renameLabels _ hρ ih => exact .renameLabels ih hρ

private theorem ofBranch {a : Tm Φ} {ℓ : Nat} {A : τ} (hℓ : At L ℓ A) (ha : Tm.HasType Γ a A) :
    Eqv Γ (.br ℓ a) (.let₁ a (.br ℓ (.var 0))) L :=
  .extra (.br hℓ ha) (.let₁ ha (.br hℓ (.var rfl))) (.inr (.bind hℓ ha))

theorem joinedValues (h : Old Γ r s L) : ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  h.elim Paper.WithProjectionReturns.Step.valueBranches (fun h => by
    cases h
    exact ⟨.br rfl .unit, .br rfl (.var rfl)⟩)

theorem normalize_seed (h : Seed Γ r s L) (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    Paper.Extension.Eqv Seed Γ r.bindBranchArguments s.bindBranchArguments L := by
  have step : Paper.Extension.Eqv Seed Γ r s L := .extra hr.hasType hs.hasType h
  exact (Paper.Extension.Eqv.paper (.cfgEta (.native hr.bindBranchArguments_equiv.symm))).trans
    (step.trans (.paper (.cfgEta (.native hs.bindBranchArguments_equiv))))

theorem eqv_normalize_of_guardedSeed
    (guarded : ∀ {Γ r s L}, Seed Γ r s L → ValueBranches Γ r L ∧ ValueBranches Γ s L)
    (h : Paper.Extension.Eqv (AddBinding Seed) Γ r s L) :
    Paper.Extension.Eqv Seed Γ r.bindBranchArguments s.bindBranchArguments L := by
  apply h.bindBranchArguments_into
  intro Γ r s L step
  rcases step with h | h
  · obtain ⟨hr, hs⟩ := guarded h
    exact normalize_seed h hr hs
  · cases h with
    | bind hℓ ha =>
      exact .let₁ ha (.paper (.cfgEta (.native
        (ValueBranches.bindBranchArguments_equiv (.br hℓ (.var rfl))))))

theorem eqv_normalize (h : Eqv Γ r s L) : JoinedEqv Γ r.bindBranchArguments s.bindBranchArguments L :=
  eqv_normalize_of_guardedSeed joinedValues h

theorem bindBranchArguments_eqv (hr : HasType Γ r L) : Eqv Γ r r.bindBranchArguments L := by
  induction hr with
  | br hℓ ha => exact ofBranch hℓ ha
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedBranchBinding
