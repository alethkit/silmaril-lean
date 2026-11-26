module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Uniqueness.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Reflection.Extensions.Defs

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Reflection.Extensions.Thms

/-! # The term-case boundary for the singleton generator proof -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedSingletonUniquenessBoundary

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithProjectionReturnsAndUnitEta (Step)
open Paper.WithProjectionReturnsAndUnitEta.Uniqueness
open Paper.Extension.Singleton (sumCofan sumCofanIsColimit ofRegion)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open CfgEta.TypeCategory (caseValueBranches returnRegion_typed)

open Paper.TypeCategory.ITree.Reflection (Op Atom Output payload projectionUnit regionArrow termArrow termCase_quotient_boundary)

local notation "FixtureSeed" => Step (τ := Ty Atom) (Φ := Op)
local notation "FixtureLit" => ofRegion FixtureSeed

private theorem swapLeft : ValueBranches [payload] (.br 0 (.inr (.var 0)) : Region Op) [Output] :=
  .br rfl (.inr (.var rfl))

private theorem swapRight : ValueBranches [payload] (.br 0 (.inl (.var 0)) : Region Op) [Output] :=
  .br rfl (.inl (.var rfl))

private theorem swapRegion : ValueBranches [Output]
    (.case (.var 0) (.br 0 (.inr (.var 0))) (.br 0 (.inl (.var 0))) : Region Op) [Output] :=
  caseValueBranches swapLeft swapRight

set_option backward.isDefEq.respectTransparency false in
theorem case_return_decomposition_boundary :
    let swap := exactCopair FixtureSeed (sumCofan FixtureSeed payload payload).inr
      (sumCofan FixtureSeed payload payload).inl
    let factor := exactCopair FixtureSeed swap (primitive Op.poll)
    Generated factor ∧ projectionUnit.map regionArrow = factor ∧
      (sumCofan FixtureSeed Output payload).inl ≫ projectionUnit.map termArrow ≠ swap := by
  let c := sumCofan FixtureSeed payload payload
  have swap : exactCopair FixtureSeed c.inr c.inl = FixtureLit swapRegion := by
    change exactCopair FixtureSeed (projectionUnit.map (Paper.TypeCategory.sumCofan payload payload).inr)
      (projectionUnit.map (Paper.TypeCategory.sumCofan payload payload).inl) = _
    rw [Paper.TypeCategory.sumCofan_inr, Paper.TypeCategory.sumCofan_inl]
    exact exactCopair_ofRegion swapLeft swapRight
  have region : exactCopair FixtureSeed (FixtureLit swapRegion) (primitive Op.poll) =
      projectionUnit.map regionArrow := by
    exact exactCopair_ofRegion swapRegion (returnRegion_typed (.op (.var rfl)))
  dsimp only
  refine ⟨.copair (.copair (.inr _ _) (.inl _ _)) (.primitive _), ?_, ?_⟩
  · rw [swap, region]
  · intro h
    apply termCase_quotient_boundary.2
    conv_rhs => rw [← region, ← swap]
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit FixtureSeed Output payload)
    · have hc := (sumCofanIsColimit FixtureSeed Output payload).fac
        (BinaryCofan.mk (exactCopair FixtureSeed c.inr c.inl) (primitive Op.poll)) ⟨WalkingPair.left⟩
      exact h.trans hc.symm
    · have hc := (sumCofanIsColimit FixtureSeed Output payload).fac
        (BinaryCofan.mk (exactCopair FixtureSeed c.inr c.inl) (primitive Op.poll)) ⟨WalkingPair.right⟩
      have leftTerm : ValueBranches [Output]
          (.let₁ (.case (.var 0) (.inr (.var 0)) (.inl (.var 0))) (.br 0 (.var 0)) : Region Op) [Output] :=
        .let₁ (.case (.var rfl) (.inr (.var rfl)) (.inl (.var rfl))) (.br rfl (.var rfl))
      have rightTerm := returnRegion_typed (.op (f := Op.poll) (.var (i := 0) (show At [payload] 0 payload from rfl)))
      have beta := Paper.RetainedCase.case_ofRegion_inr leftTerm rightTerm
      exact (((projectionUnit).map_comp _ _).symm.trans (congrArg (projectionUnit).map beta)).trans hc.symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedSingletonUniquenessBoundary
