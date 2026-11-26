module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open SubZero (model word)
open Diamond (Val dataPorts)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word]

/-- The first three binary bindings depend only on literals after preceding
folds. The last two read the argument directly or through another producer. -/
private def original : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 2) .nil
      (.cons .add (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
        (.cons .sub (.cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil))
          (.cons .mul (.cons (.output (3 : Fin 4) .head) (.cons (.output (1 : Fin 4) .head) .nil))
            (.cons .add (.cons (.arg .head) (.cons (.output (4 : Fin 5) .head) .nil))
              (.cons .sub (.cons (.output (5 : Fin 6) .head) (.cons (.output (1 : Fin 6) .head) .nil))
                .nil))))))
  result := .output (6 : Fin 7) .head

private def expected : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 2) .nil
      (.cons (.literal 1) .nil
        (.cons (.literal 0xffffffffffffffff) .nil
          (.cons (.literal 0xfffffffffffffffe) .nil
            (.cons .add (.cons (.arg .head) (.cons (.output (4 : Fin 5) .head) .nil))
              (.cons .sub (.cons (.output (5 : Fin 6) .head) (.cons (.output (1 : Fin 6) .head) .nil))
                .nil))))))
  result := .output (6 : Fin 7) .head

theorem folds_literal_chain_and_retains_nonliteral_bindings :
    ConstantFold.fold original = expected := rfl

private def entry (x : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) := .cons x .nil

theorem preserves_wraparound :
    (ConstantFold.fold original).eval model (entry 0) = (0xfffffffffffffffc : BitVec 64) :=
  (ConstantFold.fold_eval_eq original (entry 0)).trans rfl

theorem return_still_depends_on_argument :
    (ConstantFold.fold original).eval model (entry 5) = (1 : BitVec 64) :=
  (ConstantFold.fold_eval_eq original (entry 5)).trans rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Regression
