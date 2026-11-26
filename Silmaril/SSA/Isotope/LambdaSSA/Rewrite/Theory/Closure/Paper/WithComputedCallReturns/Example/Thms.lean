module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ComputedCall

/-! # The computed-call equation is independent of the ordered-pair join -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.Example

open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Paper.Extension.Singleton (ofRegion)
open Paper.Extension.Singleton.Generation (Generated)

/-- The ordered-pair join keeps the exact nested and sequenced returns distinct. -/
theorem computed_call_fails (pe : Bool) :
    ¬ Paper.Extension.Eqv (WithPairReturns.JoinedStep pe) [Payload]
      (returnRegion nested) (returnRegion sequenced) [Payload] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.computed_call_fails pe

/-- The ordered-pair join cannot supply the general computed-call agreement. -/
theorem callReturnAgreement_fails (pe : Bool) :
    ¬ WithPairReturns.CallReturnAgreement (WithPairReturns.JoinedStep (τ := Ty Atom) (Φ := Op) pe) :=
  fun agreement => computed_call_fails pe (agreement Op.consume operand_typed)

/-- The opt-in equation identifies the same two guarded returns. -/
theorem nested_eq_sequenced (pe : Bool) :
    ofRegion (JoinedStep pe) (returnRegion_typed nested_typed) =
      ofRegion (JoinedStep pe) (returnRegion_typed sequenced_typed) :=
  (Paper.Extension.Singleton.ofRegion_eq_iff (JoinedStep pe) _ _).2
    (callReturnAgreement pe Op.consume operand_typed)

/-- The opt-in induction generates the nested call, including its computed argument. -/
theorem nested_generated (pe : Bool) :
    Generated (JoinedStep pe) (ofRegion (JoinedStep pe) (returnRegion_typed nested_typed)) := by
  have input : Tm.BranchValue [Payload] (.var 0 : Tm Op) Payload := .var rfl
  have arg : WithPairReturns.ReturnFragmentWithCalls pe true operand_typed :=
    .seq (.primitive Op.produce input) (.value input)
  exact generated_returnFragment pe (.call Op.consume rfl arg)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.Example
