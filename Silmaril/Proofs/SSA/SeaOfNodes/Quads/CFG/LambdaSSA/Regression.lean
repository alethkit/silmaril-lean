module

import Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Run.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA

open RVSDG (Port Tuple)
open Diamond (ValueSort dataPorts)
open Diamond.LambdaSSA (Primitive encode inputEnv instruction)
open Silmaril.Isotope.LambdaSSA

private abbrev number : ValueSort Unit := .data ()
private abbrev regs : List (ValueSort Unit) := [number, .predicate]
private abbrev ports := dataPorts regs

private inductive Arithmetic : Diamond.Signature Unit where
  | inc : Arithmetic [number] number
  | invert : Arithmetic [.predicate] .predicate

private def arithmetic : Diamond.Model Arithmetic where
  value _ := Nat
  run
    | .inc, .cons x .nil => Nat.succ x
    | .invert, .cons p .nil => ⟨!p.down⟩

private def x : Port ports (.value number) := .head
private def guard : Port ports (.value .predicate) := .tail .head

private def cfg : Graph Arithmetic regs 4 :=
  let start : Graph Arithmetic regs 1 := .entry [⟨_, _, guard, .invert, .cons guard .nil⟩]
  let arm := start.snoc ⟨0, []⟩ [⟨_, _, x, .inc, .cons x .nil⟩]
  let join := arm.snoc ⟨0, [1]⟩ []
  join.snoc ⟨2, [2]⟩ []

private def e01 : Edge cfg 0 := .earlier (.earlier (.latest 0))
private def e02 : Edge cfg 0 := .earlier (.latest 0)
private def e12 : Edge cfg 1 := .earlier (.latest 1)
private def e23true : Edge cfg 2 := .latest 0
private def e23false : Edge cfg 2 := .latest 1

private def exitAt : (i : Fin 4) → CFG.Terminator cfg i number :=
  Fin.cases (.branch guard e01 e02 (fun h => by cases congrArg Edge.target h))
    (Fin.cases (.jump e12)
      (Fin.cases (.branch guard e23true e23false (fun h => by cases congrArg Edge.slot h))
        (fun _ => .ret x)))

private theorem onlySlot (slot : Fin 1) : slot = 0 :=
  Fin.eq_of_val_eq (by have := slot.isLt; omega)

private def program : Program cfg number where
  terminator := exitAt
  covers := by
    intro source edge
    cases edge with
    | latest slot =>
      cases slot using Fin.cases with
      | zero => exact .head _
      | succ slot =>
        have eq := onlySlot slot
        subst slot
        exact .tail _ (.head _)
    | earlier edge =>
      cases edge with
      | latest slot =>
        cases slot using Fin.cases with
        | zero => exact .tail _ (.head _)
        | succ slot =>
          have eq := onlySlot slot
          subst slot
          exact .head _
      | earlier edge =>
        cases edge with
        | latest slot =>
          have eq := onlySlot slot
          subst slot
          exact .head _
        | earlier edge => cases edge

private def input (condition : Bool) : Bank arithmetic regs := .cons (3 : Nat) (.cons ⟨condition⟩ .nil)

private def followingArm : Path cfg 2 := e12.take (e01.take cfg.start.2)
private def bypassingArm : Path cfg 2 := e02.take cfg.start.2

-- The first branch reads the newly emitted let, and the first join places
-- x's Φ from the entry value and the arm's producer respectively.
private def testedIndex : Isotope.LambdaSSA.Terminator (Primitive Arithmetic) → Option Nat
  | .case (.var i) _ _ => some i
  | _ => none

example : testedIndex (terminators program 0) = some 0 := rfl
example : (boundOperand e02 x).versions.incoming = .input := rfl
example : (boundOperand e12 x).versions.incoming = .write 1 0 := rfl
example : (boundOperand e12 x).versions.bound = .phi 2 := rfl
example : (boundOperand e23true x).versions.bound = .phi 2 := rfl

private def trueBank := followingArm.eval arithmetic (input false)
private def falseBank := bypassingArm.eval arithmetic (input true)
private abbrev trueOcc := selectedOccurrence program arithmetic trueBank 2
private abbrev falseOcc := selectedOccurrence program arithmetic falseBank 2

example : trueOcc.target = falseOcc.target := rfl
example : occurrenceEdge program trueOcc = some e23true := rfl
example : occurrenceEdge program falseOcc = some e23false := rfl
example : trueOcc ≠ falseOcc :=
  selected_distinct program arithmetic trueBank falseBank e23true e23false rfl rfl (by decide)

private theorem falseResult : (program.run arithmetic (input false)).result = (4 : Nat) := by
  have run := (program.run_iff arithmetic (input false)
    ⟨3, e23true.take followingArm, (4 : Nat)⟩).mpr
      ⟨.edge (.edge (.edge .entry e01 rfl) e12 rfl) e23true rfl, rfl⟩
  exact congrArg Outcome.result run

private theorem trueResult : (program.run arithmetic (input true)).result = (3 : Nat) := by
  have run := (program.run_iff arithmetic (input true)
    ⟨3, e23false.take bypassingArm, (3 : Nat)⟩).mpr
      ⟨.edge (.edge .entry e02 rfl) e23false rfl, rfl⟩
  exact congrArg Outcome.result run

example : Semantics.Region.Eval (instruction arithmetic) (inputEnv arithmetic (input false))
    (lower program) () 0 (.pair (encode arithmetic (sort := number) (4 : Nat)) .unit) () :=
  (returns_iff program arithmetic _ _ _).mpr falseResult

example : Semantics.Region.Eval (instruction arithmetic) (inputEnv arithmetic (input true))
    (lower program) () 0 (.pair (encode arithmetic (sort := number) (3 : Nat)) .unit) () :=
  (returns_iff program arithmetic _ _ _).mpr trueResult

end Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA
