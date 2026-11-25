module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.SequencingObstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Instance.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction.Category

/-! # Native sequencing and fixpoint counterexamples -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.SequencingObstruction

open CategoryTheory CategoryTheory.Limits
open SyntacticCategory (ofType iterateRegion)

theorem producer_valueBranches :
    ValueBranches [stateType] producer [.coprod .unit stateType] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing.producer_valueBranches

theorem sequencing_typed :
    HasType [stateType] unfolded [.unit] ∧ HasType [stateType] sequenced [.unit] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing.sequencing_typed

/-- The current native rules cannot move this one-block recursive CFG through
sequencing with the effectful producer, even though all its branch arguments
are constructor values. -/
theorem sequencing_obstruction :
    ¬ SubstitutionEquiv [stateType] unfolded sequenced [.unit] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing.sequencing_obstruction

theorem fixpoint_typed :
    HasType [stateType] (iterateRegion stateType producer) [.unit] ∧
      HasType [stateType] (producer.lsubst (fun _ => returnOrRepeat)) [.unit] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing.fixpoint_typed

/-- Native CFG feedback is inequivalent to its step followed by the
return-or-repeat case for this exactly typed producer. -/
theorem fixpoint_obstruction :
    ¬ SubstitutionEquiv [stateType] (iterateRegion stateType producer)
      (producer.lsubst (fun _ => returnOrRepeat)) [.unit] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing.fixpoint_obstruction

/-- The native iteration operation on the quotient fails the Elgot fixpoint
law for an arrow from the three-state input to the chosen coproduct of the
unit result and the input. -/
theorem categorical_fixpoint_obstruction :
    let X : SyntacticCategory Instruction ([] : VCtx (Ty Empty)) := ofType stateType
    let Y : SyntacticCategory Instruction ([] : VCtx (Ty Empty)) := ofType (Ty.unit : Ty Empty)
    ∃ f : X ⟶ Y ⨿ X, CategoryTheory.iterate f ≠ f ≫ coprod.desc (𝟙 Y) (CategoryTheory.iterate f) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing.categorical_fixpoint_obstruction

end Silmaril.Isotope.LambdaSSA.Region.SequencingObstruction
