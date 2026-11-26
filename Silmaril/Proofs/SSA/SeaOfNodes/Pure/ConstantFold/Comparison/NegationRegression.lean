module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.NegationRegression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold.Comparison (fold fold_eval_eq model)
open SubZero (word)
open Diamond (Val dataPorts)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word]

/-- A literal equality exposes two successive Not folds. The second
equality and its Not depend on the program argument. -/
private def original : Program ConstantFold.Comparison.Opcode inputs .predicate where
  dataflow := .cons (.arithmetic (.literal 7)) .nil
    (.cons (.arithmetic (.literal 8)) .nil
      (.cons .eq (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
        (.cons .not (.cons (.output (2 : Fin 3) .head) .nil)
          (.cons .not (.cons (.output (3 : Fin 4) .head) .nil)
            (.cons .eq (.cons (.arg .head) (.cons (.output (0 : Fin 5) .head) .nil))
              (.cons .not (.cons (.output (5 : Fin 6) .head) .nil) .nil))))))
  result := .output (3 : Fin 7) .head

private def expected : Program ConstantFold.Comparison.Opcode inputs .predicate where
  dataflow := .cons (.arithmetic (.literal 7)) .nil
    (.cons (.arithmetic (.literal 8)) .nil
      (.cons (.boolean false) .nil
        (.cons (.boolean true) .nil
          (.cons (.boolean false) .nil
            (.cons .eq (.cons (.arg .head) (.cons (.output (0 : Fin 5) .head) .nil))
              (.cons .not (.cons (.output (5 : Fin 6) .head) .nil) .nil))))))
  result := .output (3 : Fin 7) .head

theorem folds_comparison_then_negation_and_retains_nonconstant_negation :
    fold original = expected := rfl

private def entry (value : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons value .nil

theorem preserves_literal_inequality (value : BitVec 64) :
    ((fold original).eval model (entry value)).down = true :=
  congrArg ULift.down ((fold_eval_eq original (entry value)).trans rfl)

private def dynamic : Program ConstantFold.Comparison.Opcode inputs .predicate :=
  { original with result := .output (6 : Fin 7) .head }

theorem retained_negation_distinguishes_equal_and_unequal_inputs :
    ((fold dynamic).eval model (entry 7)).down = false ∧
      ((fold dynamic).eval model (entry 8)).down = true := ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.NegationRegression
