module

import Silmaril.SSA.SeaOfNodes.GVN.Pass.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN
open Silmaril.SSA.SeaOfNodes.GVN.Pass
open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts)
open Silmaril.SSA.RVSDG (Tuple Wires)

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
private abbrev result : List (Ty Unit) := [.value int]

private def inputs {past : List (List (Ty Unit))} : Wires args past args :=
  .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)

/-- Nodes 0 and 1 compute x − y. Nodes 2 and 3 subtract x from the values
of nodes 0 and 1 respectively. Node 4 subtracts the value of node 1 from x. -/
private def flow : Dataflow Arithmetic args [] [result, result, result, result, result] :=
  .cons .sub inputs
    (.cons .sub inputs
      (.cons .sub (.cons (.output (0 : Fin 2) .head) (.cons (.arg .head) .nil))
        (.cons .sub (.cons (.output (1 : Fin 3) .head) (.cons (.arg .head) .nil))
          (.cons .sub (.cons (.arg .head) (.cons (.output (1 : Fin 4) .head) .nil)) .nil))))

private def firstDuplicate : Producer flow int := .later .here
private def secondDuplicate : Producer flow int := .later (.later (.later .here))
private def reversed : Producer flow int := .later (.later (.later (.later .here)))

private def first := Elimination.erase firstDuplicate (newest (past := []) .head)

private def afterRedirect : Producer first.flow int := .later (.later .here)
private def afterRepresentative : Producer first.flow int := .later .here

theorem second_match_appears_after_redirect :
    Discovery.findRepresentative? secondDuplicate = none ∧
    step? flow = some first ∧
    Discovery.findRepresentative? afterRedirect = some afterRepresentative := ⟨rfl, rfl, rfl⟩

theorem one_fuel_deletes_once :
    (run 1 flow).deletions = 1 ∧ (run 1 flow).rewrite.flow = first.flow := ⟨rfl, rfl⟩

private def final := normalize flow

private def expected : Dataflow Arithmetic args [] [result, result, result] :=
  .cons .sub inputs
    (.cons .sub (.cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil))
      (.cons .sub (.cons (.arg .head) (.cons (.output (0 : Fin 2) .head) .nil)) .nil))

theorem exact_rewritten_table :
    final.rewrite.flow = expected ∧ final.deletions = 2 := ⟨rfl, rfl⟩

private def survivingReverse : Producer final.rewrite.flow int := .later (.later .here)

theorem reversed_operands_survive :
    Discovery.findRepresentative? survivingReverse = none := rfl

private def input : Tuple (Val model.value) args := .cons (10 : Int) (.cons (3 : Int) .nil)

theorem composed_routing_preserves_distinct_results :
    Diamond.read model (final.rewrite.route secondDuplicate.origin) input
      (final.rewrite.flow.eval model input PUnit.unit) = (-3 : Int) ∧
    Diamond.read model (final.rewrite.route reversed.origin) input
      (final.rewrite.flow.eval model input PUnit.unit) = (3 : Int) := by
  have agree := run_sound 6 flow model input PUnit.unit
  exact ⟨(agree _ secondDuplicate.origin).symm.trans rfl, (agree _ reversed.origin).symm.trans rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.Regression
