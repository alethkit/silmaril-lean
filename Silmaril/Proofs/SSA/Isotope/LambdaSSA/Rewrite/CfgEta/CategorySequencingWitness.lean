module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Obstruction.Defs

/-! # Strictness of the one-block CFG η quotient -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta

open CategoryTheory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Region.CfgEta (fromNative toHom_eq_iff)
open Region.CfgEta.SequencingWitness
open Region.SequencingObstruction (stateType producer_valueBranches fixpoint_obstruction)

theorem sequencingWitness_native_distinct : loop ≠ unrolled := by
  intro h
  exact fixpoint_obstruction ((Quotient.exact h) (ℓ := 0) (A := stateType) rfl)

theorem sequencingWitness_enlarged_equal : fromNative.map loop = fromNative.map unrolled := by
  apply toHom_eq_iff.mpr
  intro i A hi
  change At [stateType] i A at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact Region.CfgEta.fixpoint producer_valueBranches
  | succ i => simp [At] at hi

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta
