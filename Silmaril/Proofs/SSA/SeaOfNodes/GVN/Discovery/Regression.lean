module

import Silmaril.SSA.SeaOfNodes.GVN.Discovery.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Discovery.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN
open Silmaril.SSA.SeaOfNodes.GVN.Discovery
open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts)
open Silmaril.SSA.RVSDG (Tuple Wires)

private abbrev int : ValueSort Unit := .data ()

private inductive Arithmetic : Signature Unit where
  | test : Arithmetic [] .predicate
  | sub : Arithmetic [int, int] int

local instance : DecidableEq (ValueSort Unit) := fun a b =>
  match a, b with
  | .predicate, .predicate | .data (), .data () => isTrue rfl
  | .predicate, .data _ | .data _, .predicate => isFalse (fun h => by cases h)

local instance (ins : List (ValueSort Unit)) (out : ValueSort Unit) :
    DecidableEq (Arithmetic ins out) := fun a b => by
  cases a <;> cases b <;> exact isTrue rfl

private def model : Model Arithmetic where
  value _ := Int
  run
    | .test, .nil => ⟨true⟩
    | .sub, .cons x (.cons y .nil) => Int.sub x y

private abbrev args : List (Ty Unit) := dataPorts [int, int]
private abbrev result : List (Ty Unit) := [.value int]
private abbrev testResult : List (Ty Unit) := [.value .predicate]

private def forward {past : List (List (Ty Unit))} : Wires args past args :=
  .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)

private def backward {past : List (List (Ty Unit))} : Wires args past args :=
  .cons (.arg (.tail .head)) (.cons (.arg .head) .nil)

/-- Node 0 has a different sort. Nodes 1 and 3 are both eligible for node 4.
Node 2 reverses the operands of every preceding subtraction. -/
private def flow : Dataflow Arithmetic args [] [testResult, result, result, result, result] :=
  .cons .test .nil
    (.cons .sub forward
      (.cons .sub backward
        (.cons .sub forward
          (.cons .sub forward .nil))))

private def first : Producer flow int := .later .here
private def reversed : Producer flow int := .later (.later .here)
private def duplicate : Producer flow int := .later (.later (.later .here))
private def candidate : Producer flow int := .later (.later (.later (.later .here)))

theorem skips_other_sort :
    (earlier candidate).map (fun producer => producer.origin.producer) = [some 1, some 2, some 3] := rfl

theorem first_match_is_stable :
    checkRepresentative candidate first = true ∧
    checkRepresentative candidate duplicate = true ∧
    findRepresentative? candidate = some first := ⟨rfl, rfl, rfl⟩

theorem rejects_reversed_operands :
    (earlier reversed).map (fun producer => producer.origin.producer) = [some 1] ∧
    checkRepresentative reversed first = false ∧
    findRepresentative? reversed = none := ⟨rfl, rfl, rfl⟩

private def input : Tuple (Val model.value) args := .cons (10 : Int) (.cons (3 : Int) .nil)

theorem operand_order_changes_value :
    Diamond.read model first.origin input (flow.eval model input PUnit.unit) = (7 : Int) ∧
    Diamond.read model reversed.origin input (flow.eval model input PUnit.unit) = (-7 : Int) :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Discovery.Regression
