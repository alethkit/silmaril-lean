module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BranchBindingReturnSeeds

/-! # Branch normalization for the canonical return joins -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] {pe : ε} {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

local notation "Seed" => WithCaseAndUnaryReturns.JoinedStep (τ := τ) (Φ := Φ) pe

/-- The case-return equation already branches only on constructor values. -/
theorem case_seed_valueBranches (h : WithCaseReturns.Step pe Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BranchBindingReturnSeeds.case_seed_valueBranches h

/-- Both generators of the canonical case and unary seed have guarded endpoints. -/
theorem caseUnarySeed_valueBranches (h : WithCaseAndUnaryReturns.Step pe Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BranchBindingReturnSeeds.caseUnarySeed_valueBranches h

/-- All generators of the canonical join have guarded endpoints. -/
theorem caseUnaryJoined_valueBranches (h : Seed Γ r s L) : ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BranchBindingReturnSeeds.caseUnaryJoined_valueBranches h

/-- Branch normalization replays the original generators in the existing joined closure. -/
theorem caseUnaryJoined_normalize_seed (h : Seed Γ r s L) :
    Extension.Eqv Seed Γ r.bindBranchArguments s.bindBranchArguments L :=
  let ⟨hr, hs⟩ := caseUnaryJoined_valueBranches h
  normalize_seed h hr hs

/-- Adjoining branch binding to the canonical join is conservative on guarded representatives. -/
theorem caseUnaryJoined_guarded_eqv_iff (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    Extension.Eqv (AddBinding Seed) Γ r s L ↔ Extension.Eqv Seed Γ r s L :=
  guarded_eqv_iff_of_guardedSeed caseUnaryJoined_valueBranches hr hs

/-- Ordered pair evaluation ends in a guarded branch on the two bound results. -/
theorem pair_seed_valueBranches (h : WithPairReturns.Step Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases h with
  | seq ha hb => exact ⟨UnaryReturn.returnOnce_valueBranches (.pair ha hb),
      WithPairReturns.pairSequence_typed ha hb⟩

local notation "PairSeed" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe

/-- Adding ordered pairs preserves the guarded endpoint property for every generator. -/
theorem pairJoined_valueBranches (h : PairSeed Γ r s L) : ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  h.elim caseUnaryJoined_valueBranches pair_seed_valueBranches

/-- Branch normalization replays the ordered-pair join with the same evaluation order. -/
theorem pairJoined_normalize_seed (h : PairSeed Γ r s L) :
    Extension.Eqv PairSeed Γ r.bindBranchArguments s.bindBranchArguments L :=
  let ⟨hr, hs⟩ := pairJoined_valueBranches h
  normalize_seed h hr hs

/-- The pair-return join has the same guarded equality after adjoining branch binding. -/
theorem pairJoined_guarded_eqv_iff (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    Extension.Eqv (AddBinding PairSeed) Γ r s L ↔ Extension.Eqv PairSeed Γ r s L :=
  guarded_eqv_iff_of_guardedSeed pairJoined_valueBranches hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
