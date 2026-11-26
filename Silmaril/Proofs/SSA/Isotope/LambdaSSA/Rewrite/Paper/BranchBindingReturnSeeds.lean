module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Constructor branches in the canonical case and unary return seeds -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BranchBindingReturnSeeds

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (returnRegion_typed)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding (joinedSeed_valueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] {pe : ε} {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

theorem case_seed_valueBranches (h : Paper.WithCaseReturns.Step pe Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases h with
  | @split A B D a b ha hb _ _ =>
      let left := (Ren.wk [] (Silmaril.coprod A B)).lift A
      let right := (Ren.wk [] (Silmaril.coprod A B)).lift B
      exact ⟨returnRegion_typed (.case (.var (i := 0) rfl) (ha.rename left) (hb.rename right)),
        .case (.var (i := 0) rfl) ((returnRegion_typed ha).renameVars left)
          ((returnRegion_typed hb).renameVars right)⟩

theorem caseUnarySeed_valueBranches (h : Paper.WithCaseAndUnaryReturns.Step pe Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  h.elim Paper.UnaryReturn.Step.valueBranches case_seed_valueBranches

theorem caseUnaryJoined_valueBranches (h : Paper.WithCaseAndUnaryReturns.JoinedStep pe Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  h.elim joinedSeed_valueBranches caseUnarySeed_valueBranches

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BranchBindingReturnSeeds
