module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Soundness
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Example.Defs

/-! # The pair sequence and mixed update have distinct observations
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend extend_rename)
open scoped Paper.BoundSimulation.Obstruction
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (Env EnvTy Result)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer (extended_same)

open Paper.UnaryReturn.Beta.Constructors
open Paper.UnaryReturn.Beta.Constructors.Example (source target update constructor)
open Paper.RetainedLet (returnOnce)

private def env : Env := fun _ => .inl .unit

private theorem env_typed : EnvTy [source] env := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .inl .unit
  | succ i => simp [At] at hi

theorem pair_sequence_fails :
    ¬ Paper.Extension.Eqv (Φ := Empty) Paper.UnaryReturn.Step [source]
      (returnOnce (.pair (.let₁ (.var 0) (.var 0)) (.var 0)))
      (pairSequence (.let₁ (.var 0) (.var 0)) (.var 0)) [product source source] := by
  intro h
  have obs := extended_same h env env_typed
  change Result.fault = .jump 0 (.pair (.inl .unit) (.inl .unit)) at obs
  cases obs

theorem fusion_cannot_sequence_constructors :
    ¬ ConstructorSequencing (τ := Ty Empty) (Φ := Empty) Paper.UnaryReturn.Step := by
  intro seq
  have leftNorm : Normalizes [source] (.let₁ (.var 0) (.var 0) : Tm Empty) (.var 0) source :=
    .let₁ (.value (.var (i := 0) rfl)) (.value (.var (i := 0) rfl))
  have rightNorm : Normalizes [source] (.var 0 : Tm Empty) (.var 0) source :=
    .value (.var (i := 0) rfl)
  exact pair_sequence_fails (seq.pair leftNorm rightNorm)

theorem mixed_state_fails :
    ¬ Paper.Extension.Eqv Paper.UnaryReturn.Step [source] (returnOnce update) (.br 0 constructor) [target] := by
  intro h
  have obs := extended_same h env env_typed
  change Result.fault = .jump 0 (.inl (.pair (.inl .unit) (.inl .unit))) at obs
  cases obs

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
