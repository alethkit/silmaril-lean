module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.MulOrderRegression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open SubZero (Opcode model word rewriteRightIdentity?)
open Diamond (Val dataPorts)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word, word]

/-- The second multiplication reads the first through its original address. -/
private def original : Program Opcode inputs word where
  dataflow := .cons (.literal 1) .nil
    (.cons (.literal 2) .nil
      (.cons .mul (.cons (.output (0 : Fin 2) .head) (.cons (.arg .head) .nil))
        (.cons .mul (.cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil))
          (.cons .mul (.cons (.arg .head) (.cons (.output (1 : Fin 4) .head) .nil))
            (.cons .mul (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
              (.cons .sub (.cons (.output (1 : Fin 6) .head) (.cons (.arg .head) .nil))
                (.cons .mul (.cons (.output (1 : Fin 7) .head) (.cons (.output (1 : Fin 7) .head) .nil))
                  .nil)))))))
  result := .output (3 : Fin 8) .head

private def expected : Program Opcode inputs word where
  dataflow := .cons (.literal 1) .nil
    (.cons (.literal 2) .nil
      (.cons .mul (.cons (.arg .head) (.cons (.output (0 : Fin 2) .head) .nil))
        (.cons .mul (.cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil))
          (.cons .mul (.cons (.arg .head) (.cons (.output (1 : Fin 4) .head) .nil))
            (.cons .mul (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
              (.cons .sub (.cons (.output (1 : Fin 6) .head) (.cons (.arg .head) .nil))
                (.cons (.literal 4) .nil .nil)))))))
  result := .output (3 : Fin 8) .head

theorem swaps_literal_left_mul_and_keeps_other_operand_order :
    ConstantFold.fold original = expected := rfl

theorem exposes_multiplication_by_one :
    (rewriteRightIdentity? .mul original (.later (.later .here)) .here).isSome = false ∧
    (rewriteRightIdentity? .mul (ConstantFold.fold original) (.later (.later .here)) .here).isSome = true :=
  ⟨rfl, rfl⟩

private def entry (x y : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons x (.cons y .nil)

theorem preserves_downstream_modular_overflow :
    (ConstantFold.fold original).eval model (entry 0x7fffffffffffffff 0) =
      (0xfffffffffffffffe : BitVec 64) :=
  (ConstantFold.fold_eval_eq original (entry 0x7fffffffffffffff 0)).trans rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.MulOrderRegression
