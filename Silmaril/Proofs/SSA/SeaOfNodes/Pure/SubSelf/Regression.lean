module

import Silmaril.SSA.SeaOfNodes.Pure.SubSelf.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubSelf.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open SubSelf (fold? step? step_eval_eq)
open SubZero (model word)
open Diamond (Val dataPorts)
open GVN (Producer)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word, word]

/-- The first subtraction reads the same nonliteral producer twice.
The following subtraction reads distinct argument positions. -/
private def original : Program SubZero.Opcode inputs word where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons .sub (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons .sub (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
        (.cons .sub (.cons (.output (1 : Fin 3) .head) (.cons (.arg (.tail .head)) .nil))
          .nil)))
  result := .output (3 : Fin 4) .head

private def expected : Program SubZero.Opcode inputs word where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons (.literal 0) .nil
      (.cons .sub (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
        (.cons .sub (.cons (.output (1 : Fin 3) .head) (.cons (.arg (.tail .head)) .nil))
          .nil)))
  result := .output (3 : Fin 4) .head

private def distinct : Producer original.dataflow word := .later (.later .here)

theorem replaces_shared_subtraction_in_place : step? original = some expected := rfl

theorem refuses_distinct_sources_and_wrong_opcode :
    fold? original distinct = none ∧ fold? original .here = none ∧ step? expected = none :=
  ⟨rfl, rfl, rfl⟩

private def entry (x y : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons x (.cons y .nil)

theorem downstream_read_preserves_wraparound :
    expected.eval model (entry 0 1) = (0xffffffffffffffff : BitVec 64) :=
  (step_eval_eq replaces_shared_subtraction_in_place (entry 0 1)).trans rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubSelf.Regression
