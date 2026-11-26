module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.TriplingComputedCallFeedback

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUnaryProducer

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example (singleBind_typed singleBindArrow)
open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Paper.WithComputedCallReturns.Example (Op Payload sequenced_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample (keepInput_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example
  (Seed explicitArrow)
open Paper.Extension.Singleton (ofRegion)
open Paper.RetainedLet (returnOnce_typed)
open CfgEta.TypeCategory (returnRegion_typed)

open Paper.WithComputedCallReturns.Example (Atom)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample (explicitSequence_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls (Step)
open Paper.Extension.Singleton (ofRegion_eq_iff)
open BoundSimulation.Obstruction.Observer (EnvTy Result)
open scoped Paper.BoundSimulation.Obstruction BoundSimulation.Obstruction.Observer.CanonicalUnit
open BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation SameWith evalReturnRegion evalTermWith extension_same)

universe u v w
variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

private theorem computedCall_same {obs : TermObservation (α := α) Φ}
    (evaluate : obs.evaluateCallOperand = true)
    {Γ L : List (Ty α)} {r s : Region Φ}
    (step : Paper.WithComputedCallReturns.Step Γ r s L) : SameWith obs Γ r s := by
  cases step with
  | @seq a p ha =>
    intro env he
    let call : Tm.HasType (instrSrc p :: Γ) (.op p (.var 0)) (instrTrg p) := .op (.var rfl)
    rw [evalReturnRegion (observation := obs) (.op ha) he, evalReturnRegion (observation := obs) (.let₁ ha call) he]
    simp only [evalTermWith, evaluate, ↓reduceIte]
    cases evalTermWith obs a env <;> rfl

private theorem computedExtension_same {obs : TermObservation (α := α) Φ}
    (unmarked : obs.caseTerm = false) (evaluate : obs.evaluateCallOperand = true)
    {Γ L : List (Ty α)} {r s : Region Φ}
    (eq : Paper.Extension.Eqv (Step (τ := Ty α) (Φ := Φ) pe) Γ r s L) :
    SameWith obs Γ r s :=
  extension_same (fun step => step.elim
    (TriplingComputedCallFeedback.withTriplingSeed_same pe unmarked)
    (computedCall_same evaluate)) eq

private def observationForProducer : TermObservation (α := Atom) Op where
  boundUnaryLet := true
  evaluateCallOperand := true
  callResult _ := some .unit
  callResult_typed _ _ _ h := Option.some.inj h ▸ .base

private theorem env_typed : EnvTy [Payload] (fun _ => .unit) := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .base
  | succ i => simp [At] at hi

theorem retained_ne : explicitArrow ≠ singleBindArrow := by
  intro equal
  have rewrite := (ofRegion_eq_iff Seed explicitSequence_typed singleBind_typed).mp equal
  have seen := computedExtension_same false (obs := observationForProducer) rfl rfl rewrite
    (fun _ => .unit) env_typed
  change Result.jump 0 (.pair .unit .unit) = .fault at seen
  cases seen

theorem root_ne :
    ofRegion Seed (returnRegion_typed sequenced_typed) ≠ ofRegion Seed (returnOnce_typed sequenced_typed) := by
  intro equal
  have rewrite := (ofRegion_eq_iff Seed _ _).mp equal
  exact retained_ne ((ofRegion_eq_iff Seed explicitSequence_typed singleBind_typed).2
    (.lsubstPost rewrite (returnRegion_typed sequenced_typed) (returnOnce_typed sequenced_typed)
      (fun _ _ hi => (keepInput_typed hi).hasType)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUnaryProducer
