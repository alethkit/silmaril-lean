module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.SubSelfRegression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold.Comparison (fold fold_eval_eq model)
open SubZero (word)
open Diamond (Val dataPorts)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word, word]

/-- The first subtraction shares a runtime producer. Its new zero is used
by addition and equality. The other subtraction reads distinct arguments. -/
private def original : Program ConstantFold.Comparison.Opcode inputs .predicate where
  dataflow := .cons (.arithmetic (.literal 1)) .nil
    (.cons (.arithmetic .add) (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons (.arithmetic .sub)
        (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
        (.cons (.arithmetic .add)
          (.cons (.output (2 : Fin 3) .head) (.cons (.output (0 : Fin 3) .head) .nil))
          (.cons .eq (.cons (.output (2 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil))
            (.cons .not (.cons (.output (4 : Fin 5) .head) .nil)
              (.cons (.arithmetic .sub) (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
                (.cons .eq (.cons (.output (6 : Fin 7) .head) (.cons (.output (2 : Fin 7) .head) .nil))
                  .nil)))))))
  result := .output (5 : Fin 8) .head

private def expected : Program ConstantFold.Comparison.Opcode inputs .predicate where
  dataflow := .cons (.arithmetic (.literal 1)) .nil
    (.cons (.arithmetic .add) (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons (.arithmetic (.literal 0)) .nil
        (.cons (.arithmetic (.literal 1)) .nil
          (.cons (.boolean false) .nil
            (.cons (.boolean true) .nil
              (.cons (.arithmetic .sub) (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
                (.cons .eq (.cons (.output (6 : Fin 7) .head) (.cons (.output (2 : Fin 7) .head) .nil))
                  .nil)))))))
  result := .output (5 : Fin 8) .head

theorem new_zero_feeds_arithmetic_comparison_and_not_in_one_scan :
    fold original = expected := rfl

private def entry (x y : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons x (.cons y .nil)

theorem composed_result_for_every_input (x y : BitVec 64) :
    (original.eval model (entry x y)).down = true := by
  rw [← fold_eval_eq original (entry x y), new_zero_feeds_arithmetic_comparison_and_not_in_one_scan]
  rfl

private def returnWrappedProducer : Program ConstantFold.Comparison.Opcode inputs word where
  dataflow := original.dataflow
  result := .output (1 : Fin 8) .head

theorem preserves_shared_producer_at_signed_wraparound :
    (fold returnWrappedProducer).eval model (entry 0x7fffffffffffffff 0) =
      (0x8000000000000000 : BitVec 64) :=
  (fold_eval_eq returnWrappedProducer (entry 0x7fffffffffffffff 0)).trans rfl

private def returnDistinctComparison : Program ConstantFold.Comparison.Opcode inputs .predicate :=
  { original with result := .output (7 : Fin 8) .head }

theorem distinct_sources_keep_their_runtime_result :
    ((fold returnDistinctComparison).eval model (entry 0x8000000000000000 0x8000000000000000)).down =
      true ∧
    ((fold returnDistinctComparison).eval model (entry 0x8000000000000000 0)).down = false :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.SubSelfRegression
