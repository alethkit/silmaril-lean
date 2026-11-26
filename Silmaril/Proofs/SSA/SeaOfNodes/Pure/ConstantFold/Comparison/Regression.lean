module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold.Comparison (fold fold_eval_eq model)
open SubZero (word)
open Diamond (Val dataPorts)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word]

/-- Signed maximum plus one exposes signed minimum to the comparisons.
The final comparison still reads the original argument. -/
private def original : Program ConstantFold.Comparison.Opcode inputs .predicate where
  dataflow := .cons (.arithmetic (.literal 0x7fffffffffffffff)) .nil
    (.cons (.arithmetic (.literal 1)) .nil
      (.cons (.arithmetic (.literal 0)) .nil
        (.cons (.arithmetic .add)
          (.cons (.output (0 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil))
          (.cons .slt (.cons (.output (3 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil))
            (.cons .slt (.cons (.output (2 : Fin 5) .head) (.cons (.output (3 : Fin 5) .head) .nil))
              (.cons .sle (.cons (.output (3 : Fin 6) .head) (.cons (.output (3 : Fin 6) .head) .nil))
                (.cons .eq (.cons (.output (3 : Fin 7) .head) (.cons (.output (2 : Fin 7) .head) .nil))
                  (.cons .slt (.cons (.arg .head) (.cons (.output (2 : Fin 8) .head) .nil)) .nil))))))))
  result := .output (4 : Fin 9) .head

private def expected : Program ConstantFold.Comparison.Opcode inputs .predicate where
  dataflow := .cons (.arithmetic (.literal 0x7fffffffffffffff)) .nil
    (.cons (.arithmetic (.literal 1)) .nil
      (.cons (.arithmetic (.literal 0)) .nil
        (.cons (.arithmetic (.literal 0x8000000000000000)) .nil
          (.cons (.boolean true) .nil
            (.cons (.boolean false) .nil
              (.cons (.boolean true) .nil
                (.cons (.boolean false) .nil
                  (.cons .slt (.cons (.arg .head) (.cons (.output (2 : Fin 8) .head) .nil)) .nil))))))))
  result := .output (4 : Fin 9) .head

theorem folds_signed_order_and_retains_argument_comparison :
    fold original = expected := rfl

private def entry (wordValue : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons wordValue .nil

theorem returns_true_for_signed_minimum_less_than_zero :
    ((fold original).eval model (entry 0)).down = true :=
  congrArg ULift.down ((fold_eval_eq original (entry 0)).trans rfl)

private def returnArgumentComparison : Program ConstantFold.Comparison.Opcode inputs .predicate :=
  { original with result := .output (8 : Fin 9) .head }

theorem retained_comparison_distinguishes_signed_inputs :
    ((fold returnArgumentComparison).eval model (entry 0x8000000000000000)).down = true ∧
      ((fold returnArgumentComparison).eval model (entry 0)).down = false := ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Regression
