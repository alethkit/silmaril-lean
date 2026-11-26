module

import Silmaril.SSA.SeaOfNodes.GVN.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN
open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts)
open Silmaril.SSA.RVSDG (Tuple)

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

/-- Producer zero is shared. The next two subtract the first argument from
it. The fourth performs the same operation with reversed operand positions. -/
private def flow : Dataflow Arithmetic args [] [result, result, result, result] :=
  .cons .sub (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons .sub (.cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil))
      (.cons .sub (.cons (.output (0 : Fin 2) .head) (.cons (.arg .head) .nil))
        (.cons .sub (.cons (.arg .head) (.cons (.output (0 : Fin 3) .head) .nil)) .nil)))

private def representative : Producer flow int := .later .here
private def candidate : Producer flow int := .later (.later .here)
private def reversed : Producer flow int := .later (.later (.later .here))

private def input : Tuple (Val model.value) args :=
  .cons (10 : Int) (.cons (3 : Int) .nil)

theorem accepts_sharing : checkRepresentative candidate representative = true := by decide

theorem rejects_reordering : checkRepresentative reversed representative = false := by decide

theorem rejects_later_representative : checkRepresentative representative candidate = false := by decide

theorem reordered_values_differ :
    Diamond.read model representative.origin input (flow.eval model input PUnit.unit) = (-3 : Int) ∧
    Diamond.read model reversed.origin input (flow.eval model input PUnit.unit) = (3 : Int) := by
  exact ⟨rfl, rfl⟩

theorem redirect_sound :
    Diamond.read model (redirectResult candidate representative) input (flow.eval model input PUnit.unit) =
      Diamond.read model candidate.origin input (flow.eval model input PUnit.unit) :=
  redirectResult_read candidate representative model input PUnit.unit

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Regression
