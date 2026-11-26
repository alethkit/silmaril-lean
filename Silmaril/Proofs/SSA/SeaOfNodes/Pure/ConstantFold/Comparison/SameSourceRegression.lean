module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.SameSourceRegression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold.Comparison (fold fold_eval_eq model)
open SubZero (word)
open Diamond (Val dataPorts)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word, word]

/-- Repeated reads of an input-dependent addition and of an argument are
eligible. The final equality compares distinct runtime wires. -/
private def original : Program ConstantFold.Comparison.Opcode inputs .predicate where
  dataflow := .cons (.arithmetic (.literal 1)) .nil
    (.cons (.arithmetic .add) (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons .eq (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
        (.cons .slt (.cons (.arg .head) (.cons (.arg .head) .nil))
          (.cons .sle (.cons (.output (1 : Fin 4) .head) (.cons (.output (1 : Fin 4) .head) .nil))
            (.cons .not (.cons (.output (2 : Fin 5) .head) .nil)
              (.cons .eq (.cons (.output (1 : Fin 6) .head) (.cons (.arg (.tail .head)) .nil))
                .nil))))))
  result := .output (5 : Fin 7) .head

private def expected : Program ConstantFold.Comparison.Opcode inputs .predicate where
  dataflow := .cons (.arithmetic (.literal 1)) .nil
    (.cons (.arithmetic .add) (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons (.boolean true) .nil
        (.cons (.boolean false) .nil
          (.cons (.boolean true) .nil
            (.cons (.boolean false) .nil
              (.cons .eq (.cons (.output (1 : Fin 6) .head) (.cons (.arg (.tail .head)) .nil))
                .nil))))))
  result := .output (5 : Fin 7) .head

theorem folds_same_source_and_refuses_distinct_dynamic_wires :
    fold original = expected := rfl

private def entry (x y : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons x (.cons y .nil)

theorem reflexive_equality_exposes_negation_for_all_inputs (x y : BitVec 64) :
    ((fold original).eval model (entry x y)).down = false := by
  rw [folds_same_source_and_refuses_distinct_dynamic_wires]
  rfl

private def returnWrappedWord : Program ConstantFold.Comparison.Opcode inputs word where
  dataflow := original.dataflow
  result := .output (1 : Fin 7) .head

theorem preserves_signed_boundary_wraparound :
    (fold returnWrappedWord).eval model (entry 0x7fffffffffffffff 0) =
      (0x8000000000000000 : BitVec 64) :=
  (fold_eval_eq returnWrappedWord (entry 0x7fffffffffffffff 0)).trans rfl

private def returnDistinctComparison : Program ConstantFold.Comparison.Opcode inputs .predicate :=
  { original with result := .output (6 : Fin 7) .head }

theorem retained_comparison_observes_distinct_inputs :
    ((fold returnDistinctComparison).eval model (entry 0x7fffffffffffffff 0x8000000000000000)).down =
      true ∧
    ((fold returnDistinctComparison).eval model (entry 0x7fffffffffffffff 0)).down = false :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.SameSourceRegression
