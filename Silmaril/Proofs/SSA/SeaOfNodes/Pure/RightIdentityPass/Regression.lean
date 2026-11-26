module

import Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word)
open Diamond (Val dataPorts)
open GVN (Producer)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word, word]

/-- The multiplication's right operand is initially the producer of
`1 + 0`. The downstream addition needs the multiplication and a reversed
subtraction, which is outside the right-identity matcher. -/
private def original : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 1) .nil
    (.cons (.literal 0) .nil
      (.cons .add (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
        (.cons .mul (.cons (.arg .head) (.cons (.output (2 : Fin 3) .head) .nil))
          (.cons .sub (.cons (.output (1 : Fin 4) .head) (.cons (.arg (.tail .head)) .nil))
            (.cons .add (.cons (.output (3 : Fin 5) .head) (.cons (.output (4 : Fin 5) .head) .nil))
              .nil)))))
  result := .output (5 : Fin 6) .head

private def afterAdd : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 1) .nil
    (.cons (.literal 0) .nil
      (.cons .mul (.cons (.arg .head) (.cons (.output (0 : Fin 2) .head) .nil))
        (.cons .sub (.cons (.output (1 : Fin 3) .head) (.cons (.arg (.tail .head)) .nil))
          (.cons .add (.cons (.output (2 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil))
            .nil))))
  result := .output (4 : Fin 5) .head

private def expected : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 1) .nil
    (.cons (.literal 0) .nil
      (.cons .sub (.cons (.output (1 : Fin 2) .head) (.cons (.arg (.tail .head)) .nil))
        (.cons .add (.cons (.arg .head) (.cons (.output (2 : Fin 3) .head) .nil)) .nil)))
  result := .output (3 : Fin 4) .head

private def originalMul : Producer original.dataflow word := .later (.later (.later .here))
private def remainingSub : Producer expected.dataflow word := .later (.later .here)

theorem multiplication_needs_first_redirect :
    rewriteCandidate? original (wordProducers original.dataflow) originalMul .mul = none := rfl

theorem first_redirect_exposes_literal_one : step? original = some afterAdd := rfl

theorem second_step_rewrites_downstream_read : step? afterAdd = some expected := rfl

theorem reversed_subtraction_survives :
    rewriteCandidate? expected (wordProducers expected.dataflow) remainingSub .sub = none ∧
      step? expected = none := ⟨rfl, rfl⟩

theorem normalizes_with_two_deletions : normalize original = ⟨expected, 2⟩ := rfl

private def entry : Tuple (Val model.value) (dataPorts inputs) :=
  .cons (0 : BitVec 64) (.cons (1 : BitVec 64) .nil)

theorem preserves_wrapping_return :
    (normalize original).program.eval model entry = (0xffffffffffffffff : BitVec 64) :=
  (normalize_eval_eq original entry).trans rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.Regression
