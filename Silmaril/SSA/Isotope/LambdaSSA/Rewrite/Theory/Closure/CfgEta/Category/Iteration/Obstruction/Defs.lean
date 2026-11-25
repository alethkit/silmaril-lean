module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.SequencingObstruction.Thms

/-! # The native fixpoint witness before quotienting by CFG η -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.SequencingWitness

open CategoryTheory
open Region.SequencingObstruction (Instruction stateType producer_valueBranches)
open Region.SyntacticCategory (iterateRegion_valueBranches)

@[expose] def input : ContinuationContext Instruction ([] : VCtx (Ty Empty)) :=
  ContinuationContext.single stateType

@[expose] def output : ContinuationContext Instruction ([] : VCtx (Ty Empty)) :=
  ContinuationContext.single .unit

/-- The loop on the original three-state, effectful producer. -/
@[expose] def loop : input ⟶ output :=
  ContinuationContext.singletonToHom (iterateRegion_valueBranches producer_valueBranches)

/-- The producer followed by the case that returns or reruns that loop. -/
@[expose] def unrolled : input ⟶ output :=
  (ContinuationContext.singletonToHom
    (Y := ContinuationContext.single (.coprod .unit stateType)) producer_valueBranches) ≫
  ContinuationContext.singletonToHom (Y := output)
    (TypeCategory.caseValueBranches
      (show ValueBranches [(Ty.unit : Ty Empty)] (.br 0 (.var 0) : Region Instruction) [Ty.unit] from .br rfl (.var rfl))
      (iterateRegion_valueBranches producer_valueBranches))

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.SequencingWitness
