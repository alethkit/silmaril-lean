module

import Silmaril.SSA.SeaOfNodes.Pure.SubZero.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.RightIdentityRegression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.SubZero
open Diamond (Val dataPorts)
open GVN (Producer)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word, word]

private def original : Program Opcode inputs word where
  dataflow := .cons (.literal 0) .nil
    (.cons (.literal 1) .nil
      (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 2) .head) .nil))
        (.cons .mul (.cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil))
          (.cons .add (.cons (.output (3 : Fin 4) .head) (.cons (.arg (.tail .head)) .nil)) .nil))))
  result := .output (4 : Fin 5) .head

private def afterAdd : Program Opcode inputs word where
  dataflow := .cons (.literal 0) .nil
    (.cons (.literal 1) .nil
      (.cons .mul (.cons (.arg .head) (.cons (.output (1 : Fin 2) .head) .nil))
        (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons (.arg (.tail .head)) .nil)) .nil)))
  result := .output (3 : Fin 4) .head

private def afterMul : Program Opcode inputs word where
  dataflow := .cons (.literal 0) .nil
    (.cons (.literal 1) .nil
      (.cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)) .nil))
  result := .output (2 : Fin 3) .head

private def add : Producer original.dataflow word := .later (.later .here)
private def mul : Producer afterAdd.dataflow word := .later (.later .here)

theorem add_zero_rewires_later_multiplication :
    rewriteRightIdentity? .add original add .here = some afterAdd := rfl

theorem mul_one_rewires_later_addition :
    rewriteRightIdentity? .mul afterAdd mul (.later .here) = some afterMul := rfl

theorem rejects_wrong_literal_and_opcode :
    rewriteRightIdentity? .add original add (.later .here) = none ∧
      rewrite? original add .here = none := ⟨rfl, rfl⟩

private def multiplyByZero : Program Opcode inputs word where
  dataflow := .cons (.literal 0) .nil
    (.cons .mul (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  result := .output (1 : Fin 2) .head

theorem rejects_exact_rhs_with_wrong_value :
    rewriteRightIdentity? .mul multiplyByZero (.later .here) .here = none := rfl

private def entry (x y : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons x (.cons y .nil)

theorem preserves_modular_wraparound :
    afterMul.eval model (entry 0xffffffffffffffff 1) = (0 : BitVec 64) :=
  (rightIdentity_eval_eq mul_one_rewires_later_addition _).trans
    ((rightIdentity_eval_eq add_zero_rewires_later_multiplication _).trans rfl)

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.RightIdentityRegression
