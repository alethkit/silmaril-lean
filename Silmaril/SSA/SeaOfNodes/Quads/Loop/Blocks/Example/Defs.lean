module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Defs

/-! # Shared source fixture with a preheader write and two feedback activations -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example

open RVSDG (Port Tuple)
open Diamond (ValueSort Model dataPorts)

abbrev num : ValueSort Unit := .data ()
abbrev regs : List (ValueSort Unit) := [num, num, num, num, num, .predicate]
abbrev ports := dataPorts regs

inductive Arithmetic : Diamond.Signature Unit where
  | copy : Arithmetic [num] num
  | add : Arithmetic [num, num] num
  | pred : Arithmetic [num] num
  | positive : Arithmetic [num] .predicate

def arithmetic : Model Arithmetic where
  value _ := Nat
  run
    | .copy, .cons x .nil => x
    | .add, .cons x (.cons y .nil) => Nat.add x y
    | .pred, .cons x .nil => Nat.pred x
    | .positive, .cons x .nil => ⟨!(Nat.beq x 0)⟩

def counter : Port ports (.value num) := .head
def x : Port ports (.value num) := .tail .head
def y : Port ports (.value num) := .tail (.tail .head)
def saved : Port ports (.value num) := .tail (.tail (.tail .head))
def stride : Port ports (.value num) := .tail (.tail (.tail (.tail .head)))
def again : Port ports (.value .predicate) := .tail (.tail (.tail (.tail (.tail .head))))

def program : Program Arithmetic regs num where
  preheader := .jump [⟨_, _, x, .add, .cons y (.cons stride .nil)⟩]
  header := .branch
    [ ⟨_, _, saved, .copy, .cons x .nil⟩
    , ⟨_, _, x, .copy, .cons y .nil⟩
    , ⟨_, _, y, .add, .cons saved (.cons y .nil)⟩
    , ⟨_, _, counter, .pred, .cons counter .nil⟩
    , ⟨_, _, again, .positive, .cons counter .nil⟩ ] again y

def bank (n a b scratch increment : Nat) (test : Bool) : Bank (regs := regs) arithmetic :=
  .cons n (.cons a (.cons b (.cons scratch (.cons increment (.cons ⟨test⟩ .nil)))))

def input (n : Nat) : Bank (regs := regs) arithmetic := bank n 99 5 0 2 false

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example
