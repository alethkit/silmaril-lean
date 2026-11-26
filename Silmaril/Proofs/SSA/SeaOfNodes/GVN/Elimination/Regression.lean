module

import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN
open Silmaril.SSA.SeaOfNodes.GVN.Elimination
open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts)
open Silmaril.SSA.RVSDG (Origin Tuple)

private abbrev int : ValueSort Unit := .data ()

private inductive Arithmetic : Signature Unit where
  | sub : Arithmetic [int, int] int

local instance : DecidableEq (ValueSort Unit) := fun a b =>
  match a, b with
  | .predicate, .predicate | .data (), .data () => isTrue rfl
  | .predicate, .data _ | .data _, .predicate => isFalse (fun h => by cases h)

local instance (ins : List (ValueSort Unit)) (out : ValueSort Unit) :
    DecidableEq (Arithmetic ins out) := fun a b => by
  cases a
  cases b
  exact isTrue rfl

private def model : Model Arithmetic where
  value _ := Int
  run
    | .sub, .cons x (.cons y .nil) => Int.sub x y

private abbrev args : List (Ty Unit) := dataPorts [int, int]
private abbrev resultSig : List (Ty Unit) := [.value int]

/-- Nodes 0 and 1 compute x − y. Node 2 consumes node 1, and node 3 consumes
both node 2 and node 1. -/
private def flow : Dataflow Arithmetic args [] [resultSig, resultSig, resultSig, resultSig] :=
  .cons .sub (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons .sub (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
      (.cons .sub (.cons (.output (1 : Fin 2) .head) (.cons (.arg (.tail .head)) .nil))
        (.cons .sub (.cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil)) .nil)))

private def representative : Producer flow int := .here
private def candidate : Producer flow int := .later .here
private def output : Producer flow int := .later (.later (.later .here))
private def replacement : Origin args (operandScope candidate) (.value int) := .output (0 : Fin 1) .head
private def rewritten := erase candidate replacement

private theorem admitted : eliminate? candidate representative replacement = some rewritten := rfl

/-- Both internal uses now name vertex 0. The last binding names its other
operand at the shifted vertex 1, and only three bindings remain. -/
private def expected : Dataflow Arithmetic args [] [resultSig, resultSig, resultSig] :=
  .cons .sub (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons .sub (.cons (.output (0 : Fin 1) .head) (.cons (.arg (.tail .head)) .nil))
      (.cons .sub (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil)) .nil))

theorem rewrites_internal_uses : rewritten.flow = expected := rfl

theorem removes_one_producer : rewritten.sigs'.length = 3 :=
  Nat.succ.inj (eliminate_size candidate representative replacement admitted)

theorem remaps_addresses :
    (rewritten.route candidate.origin).address = .output 0 0 ∧
    (rewritten.route output.origin).address = .output 2 0 := ⟨rfl, rfl⟩

private def input : Tuple (Val model.value) args := .cons (10 : Int) (.cons (3 : Int) .nil)

theorem preserves_output :
    Diamond.read model (rewritten.route output.origin) input (rewritten.flow.eval model input PUnit.unit) =
      (-3 : Int) := by
  exact ((eliminate_sound candidate representative replacement model input PUnit.unit admitted)
    _ output.origin).symm.trans rfl

/-- An in-scope wire of the right sort is still refused when it is not the
representative selected by the equality check. -/
theorem rejects_wrong_prefix_wire :
    eliminate? candidate representative (.arg .head) = none := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.Regression
