module

public import Silmaril.SSA.MLIR.Affine.Defs

public section

namespace Silmaril.Proofs.MLIR.Affine

open Silmaril.MLIR.Affine

universe u

theorem runs_iff_fold {State : Type u} (upper : Int) (step : Step) (body : Block State)
    (iv : Int) (init out : State) :
    Runs upper step body iv init out ↔
      out = (iterationValues upper step iv).foldl (fun state i => body.yield i state) init := by
  constructor
  · intro run
    induction run with
    | done stop => rw [iterationValues, ite_eq_right (Int.not_lt.mpr stop), List.foldl_nil]
    | next enter _ ih => rw [iterationValues, ite_eq_left enter, List.foldl_cons, ← ih]
  · intro h
    subst out
    induction iv using iterationValues.induct upper step generalizing init with
    | case1 iv enter ih =>
      rw [iterationValues, ite_eq_left enter, List.foldl_cons]
      exact .next enter (ih _)
    | case2 iv stop =>
      rw [iterationValues, ite_eq_right stop, List.foldl_nil]
      exact .done (Int.not_lt.mp stop)

end Silmaril.Proofs.MLIR.Affine
