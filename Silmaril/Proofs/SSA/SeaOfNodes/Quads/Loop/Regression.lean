module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop

open RVSDG (Origin Port Tuple)
open Diamond (ValueSort Signature Model Ty Val dataPorts)
open Silmaril.SSA.SeaOfNodes.Loop (headerPorts)

private abbrev number : ValueSort Unit := .data ()
private abbrev regs : List (ValueSort Unit) := [number, number, number, .predicate]
private abbrev ports := dataPorts regs

private inductive Arithmetic : Signature Unit where
  | add : Arithmetic [number, number] number
  | pred : Arithmetic [number] number
  | positive : Arithmetic [number] .predicate

private def arithmetic : Model Arithmetic where
  value _ := Nat
  run
    | .add, .cons left (.cons right .nil) => Nat.add left right
    | .pred, .cons value .nil => Nat.pred value
    | .positive, .cons value .nil => ⟨!(Nat.beq value 0)⟩

private def counter : Port ports (.value number) := .head
private def total : Port ports (.value number) := .tail .head
private def stride : Port ports (.value number) := .tail (.tail .head)
private def again : Port ports (.value .predicate) := .tail (.tail (.tail .head))

private def program : Program Arithmetic regs number where
  activation :=
    .assign total .add (.cons total (.cons stride .nil))
      (.assign counter .pred (.cons counter .nil)
        (.assign again .positive (.cons counter .nil) (.ret again)))
  result := total

private def bank (n sum increment : Nat) (loopAgain : Bool) : Tuple (Val arithmetic.value) ports :=
  .cons n (.cons sum (.cons increment (.cons ⟨loopAgain⟩ .nil)))

private def headerArg {t : Ty Unit} {past : List (List (Ty Unit))}
    (port : Port ports t) : Origin (headerPorts regs regs) past t :=
  .arg (carryPort port ports)

-- The first two overwrites consume the latched ports. The guard reads the new counter.
example : program.lower.header =
    .cons .add (.cons (headerArg total) (.cons (headerArg stride) .nil))
      (.cons .pred (.cons (headerArg counter) .nil)
        (.cons .positive (.cons (.output (1 : Fin 2) .head) .nil) .nil)) := rfl

-- Entry and feedback have distinct origin columns.
example : (program.lower.phiInputs .entry).get total = .arg total := rfl
example : ((program.lower.phiInputs .backedge).get total).producer = some 0 := rfl
example : ((program.lower.phiInputs .backedge).get counter).producer = some 1 := rfl
example : (program.lower.phiInputs .backedge).get stride = headerArg stride := rfl

-- The original input differs from the current latch. The untouched stride comes from the latch.
example : program.lower.step arithmetic (bank 99 500 100 false) (bank 3 10 7 false) =
    .inr (bank 2 17 7 true) := rfl

example : program.evalBackedges arithmetic 0 (bank 1 10 7 false) = some (17 : Nat) := rfl
example : program.lower.evalBackedges arithmetic 0 (bank 1 10 7 false) = some (17 : Nat) := rfl
example : program.lower.evalBackedges arithmetic 1 (bank 3 10 7 false) = none := rfl
example : program.evalBackedges arithmetic 2 (bank 3 10 7 false) = some (31 : Nat) := rfl
example : program.lower.evalBackedges arithmetic 2 (bank 3 10 7 false) = some (31 : Nat) := rfl

private theorem sourceReturns : program.ReturnsAfter arithmetic 2 (bank 3 10 7 false) (31 : Nat) :=
  .backedge (next := bank 2 17 7 true) rfl
    (.backedge (next := bank 1 24 7 true) rfl (.exit rfl))

example : program.lower.ReturnsAfter arithmetic (bank 3 10 7 false) 2 (bank 3 10 7 false) (31 : Nat) :=
  (program.lower_returnsAfter_iff arithmetic _ _ _ _).mpr sourceReturns

end Silmaril.SSA.SeaOfNodes.Quads.Loop
