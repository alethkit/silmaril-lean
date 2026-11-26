module

import Silmaril.SSA.SeaOfNodes.Pure.WordNormalize.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.WordNormalize
open SubZero (model word)
open Diamond (Ty Val dataPorts)
open Silmaril.SSA.RVSDG (Tuple Wires)

private abbrev inputs := [word, word]
private abbrev args := dataPorts inputs

private def xy {past : List (List (Ty Unit))} : Wires args past args :=
  .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)

private def yx {past : List (List (Ty Unit))} : Wires args past args :=
  .cons (.arg (.tail .head)) (.cons (.arg .head) .nil)

/-- The two subtractions differ in their first operand until addition by
zero is erased. The reversed subtraction is a distinct key. -/
private def original : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0) .nil
    (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons .sub (.cons (.output (1 : Fin 2) .head) (.cons (.arg (.tail .head)) .nil))
        (.cons .sub xy (.cons .sub yx
          (.cons .sub (.cons (.output (3 : Fin 5) .head) (.cons (.output (4 : Fin 5) .head) .nil))
            .nil)))))
  result := .output (5 : Fin 6) .head

private def afterIdentity : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0) .nil
    (.cons .sub xy (.cons .sub xy (.cons .sub yx
      (.cons .sub (.cons (.output (2 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil))
        .nil))))
  result := .output (4 : Fin 5) .head

private def expected : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0) .nil
    (.cons .sub xy (.cons .sub yx
      (.cons .sub (.cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil))
        .nil)))
  result := .output (3 : Fin 4) .head

theorem identity_exposes_gvn_match :
    gvnStep? original = none ∧ step? original = some afterIdentity ∧
      RightIdentityPass.step? afterIdentity = none ∧ gvnStep? afterIdentity = some expected :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem removes_both_bindings_and_reroutes_return :
    normalize original = ⟨expected, 2⟩ := rfl

theorem reversed_subtraction_survives_at_fixed_point : step? expected = none := rfl

private def entry : Tuple (Val model.value) args :=
  .cons (0 : BitVec 64) (.cons (1 : BitVec 64) .nil)

theorem preserves_wrapping_emitted_return :
    (normalize original).program.lower.run (toRVSDGModel model) entry =
      .cons (0xfffffffffffffffe : BitVec 64) .nil :=
  (normalize_lower_run_eq original entry).trans rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize.Regression
