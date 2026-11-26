module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks

open RVSDG (Port Tuple)
open Diamond (ValueSort Model dataPorts)

private abbrev num : ValueSort Unit := .data ()
private abbrev regs : List (ValueSort Unit) := [num, num, num, num, num, .predicate]
private abbrev ports := dataPorts regs

private inductive Arithmetic : Diamond.Signature Unit where
  | copy : Arithmetic [num] num
  | add : Arithmetic [num, num] num
  | pred : Arithmetic [num] num
  | positive : Arithmetic [num] .predicate

private def arithmetic : Model Arithmetic where
  value _ := Nat
  run
    | .copy, .cons x .nil => x
    | .add, .cons x (.cons y .nil) => Nat.add x y
    | .pred, .cons x .nil => Nat.pred x
    | .positive, .cons x .nil => ⟨!(Nat.beq x 0)⟩

private def counter : Port ports (.value num) := .head
private def x : Port ports (.value num) := .tail .head
private def y : Port ports (.value num) := .tail (.tail .head)
private def saved : Port ports (.value num) := .tail (.tail (.tail .head))
private def stride : Port ports (.value num) := .tail (.tail (.tail (.tail .head)))
private def again : Port ports (.value .predicate) := .tail (.tail (.tail (.tail (.tail .head))))

private def program : Program Arithmetic regs num where
  preheader := .jump [⟨_, _, x, .add, .cons y (.cons stride .nil)⟩]
  header := .branch
    [ ⟨_, _, saved, .copy, .cons x .nil⟩
    , ⟨_, _, x, .copy, .cons y .nil⟩
    , ⟨_, _, y, .add, .cons saved (.cons y .nil)⟩
    , ⟨_, _, counter, .pred, .cons counter .nil⟩
    , ⟨_, _, again, .positive, .cons counter .nil⟩ ] again y

private def bank (n a b scratch increment : Nat) (test : Bool) : Bank (regs := regs) arithmetic :=
  .cons n (.cons a (.cons b (.cons scratch (.cons increment (.cons ⟨test⟩ .nil)))))

private def input (n : Nat) : Bank (regs := regs) arithmetic := bank n 99 5 0 2 false

-- The preheader creates x; the feedback defines both x and y in the
-- header's own producer scope. The untouched slot reads a pending port.
example : ((program.lower.phiInputs .entry).get x).producer = some 0 := rfl
example : ((program.lower.phiInputs .backedge).get x).producer = some 1 := rfl
example : ((program.lower.phiInputs .backedge).get y).producer = some 2 := rfl
example : (program.lower.phiInputs .backedge).get stride = .arg (carryPort stride ports) := rfl

private def first := program.latch arithmetic .entry (input 3) (input 3)
private def second := program.latch arithmetic .backedge (input 3) first
private def third := program.latch arithmetic .backedge (input 3) second

example : first = bank 3 7 5 0 2 false := rfl
example : second = bank 2 5 12 7 2 true := rfl
example : third = bank 1 12 17 5 2 true := rfl

-- A differing feedback value is used on the next activation. Zero budget
-- still permits an immediate return after the preheader and first header.
example : program.evalBackedges arithmetic 0 (input 1) = some (12 : Nat) := rfl
example : program.lower.evalBackedges arithmetic 0 (input 1) = some (12 : Nat) := rfl
example : program.evalBackedges arithmetic 1 (input 3) = none := rfl
example : program.lower.evalBackedges arithmetic 1 (input 3) = none := rfl
example : program.evalBackedges arithmetic 2 (input 3) = some (29 : Nat) := rfl
example : program.lower.evalBackedges arithmetic 2 (input 3) = some (29 : Nat) := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks
