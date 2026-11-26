module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CaseReturns
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ConstructorSoundness

/-! # A typed observation of unary lets inside primitive arguments -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedCallReturns.Example
open CfgEta.TypeCategory (returnRegion)
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer (TermObservation SameWith extension_same unary_fusion_same evalReturnRegion sequence_pair)
open scoped Paper.BoundSimulation.Obstruction Observer.CanonicalUnit
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (EnvTy Result)

private def observation : TermObservation (α := Atom) Op where
  unitCall _ := true
  unitCall_typed _ _ _ := .base

private theorem pair_join_same (pe : Bool) {Γ L : List (Ty Atom)} {r s : Region Op}
    (h : Paper.Extension.Eqv (Paper.WithPairReturns.JoinedStep pe) Γ r s L) : SameWith observation Γ r s := by
  apply extension_same (observation := observation) _ h
  intro Γ L r s step
  rcases step with (base | returned) | pair
  · exact projectionUnitSeed_same base
  · exact returned.elim unary_fusion_same (caseReturnSeed_same rfl)
  · cases pair with
    | seq ha hb => exact fun env _ => sequence_pair rfl _ _ env

private theorem env_typed : EnvTy [Payload] (fun _ => .unit) := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .base
  | succ i => simp [At] at hi

theorem computed_call_fails (pe : Bool) :
    ¬ Paper.Extension.Eqv (Paper.WithPairReturns.JoinedStep pe) [Payload]
      (returnRegion nested) (returnRegion sequenced) [Payload] := by
  intro h
  have eq := pair_join_same pe h (fun _ => .unit) env_typed
  rw [evalReturnRegion nested_typed env_typed, evalReturnRegion sequenced_typed env_typed] at eq
  change Result.fault = .jump 0 .unit at eq
  cases eq

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
