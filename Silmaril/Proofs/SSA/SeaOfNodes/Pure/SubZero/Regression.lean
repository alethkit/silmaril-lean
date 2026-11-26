module

import Silmaril.SSA.SeaOfNodes.Pure.SubZero.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.SubZero
open Diamond (Val dataPorts)
open GVN (Producer)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word, word]

/-- The chosen subtraction feeds a later subtraction. The other zero
literal has a distinct address. The final binding reverses zero and x. -/
private def fixture (literal : BitVec 64) : Program Opcode inputs word where
  dataflow := .cons (.literal literal) .nil
    (.cons (.literal 0) .nil
      (.cons .sub (.cons (.arg .head) (.cons (.output (0 : Fin 2) .head) .nil))
        (.cons .sub (.cons (.output (2 : Fin 3) .head) (.cons (.arg (.tail .head)) .nil))
          (.cons .sub (.cons (.output (0 : Fin 4) .head) (.cons (.arg .head) .nil)) .nil))))
  result := .output (3 : Fin 5) .head

private def original := fixture 0
private def candidate : Producer original.dataflow word := .later (.later .here)
private def zero : Producer original.dataflow word := .here
private def otherZero : Producer original.dataflow word := .later .here
private def reversed : Producer original.dataflow word := .later (.later (.later (.later .here)))

private def expected : Program Opcode inputs word where
  dataflow := .cons (.literal 0) .nil
    (.cons (.literal 0) .nil
      (.cons .sub (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
        (.cons .sub (.cons (.output (0 : Fin 3) .head) (.cons (.arg .head) .nil)) .nil)))
  result := .output (2 : Fin 4) .head

theorem rewires_the_user_and_shifts_the_return : rewrite? original candidate zero = some expected := rfl

theorem removes_one_binding : expected.sigs.length + 1 = original.sigs.length :=
  rewrite_count rewires_the_user_and_shifts_the_return

theorem rejects_reversed_operands : rewrite? original reversed zero = none := rfl

theorem rejects_a_different_zero_address : rewrite? original candidate otherZero = none := rfl

theorem rejects_a_nonzero_rhs : rewrite? (fixture 1) (.later (.later .here)) .here = none := rfl

private def entry (x y : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons x (.cons y .nil)

theorem preserves_modular_wraparound :
    expected.eval model (entry 0 1) = (0xffffffffffffffff : BitVec 64) :=
  (rewrite_eval_eq rewires_the_user_and_shifts_the_return (entry 0 1)).trans rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.Regression
