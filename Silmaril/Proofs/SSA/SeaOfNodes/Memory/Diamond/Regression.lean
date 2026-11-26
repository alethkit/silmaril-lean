module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond

open RVSDG (Origin Port Tuple)
open SeaOfNodes.Diamond (Projection)

private abbrev args : List ValueSort := [.address, .address, .address, .word, .word]

private def x : Address 3 := 0
private def trueCell : Address 3 := 1
private def falseCell : Address 3 := 2

private def initial : Heap 3 := fun address => if address = x then 7 else 0

private def input : Tuple (Val 3) args :=
  .cons x (.cons trueCell (.cons falseCell (.cons (11 : Word) (.cons (33 : Word) .nil))))

private def xWire {past : List (List ValueSort)} : Origin args past .address := .arg .head

-- Load the old x, copy it to the arm's own cell, and overwrite x.
private def arm (save : Port args .address) (newWord : Port args .word) : Memory.Graph args :=
  let oldX : Origin args [[.word]] .word := .output (0 : Fin 1) .head
  .load (.latest 0) xWire
    (.store (.latest 0) (.arg save) oldX
      (.store (.latest 1) xWire (.arg newWord) (.ret (.latest 2) oldX)))

-- Simple chapter 10, “Memory is an SSA variable”, with distinct saved-old-value
-- cells added so the final heap reveals whether an untaken arm wrote.
-- https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable
private def diamond (first : Projection) : Graph args where
  merge := ⟨first⟩
  arm
    | .onTrue => arm (.tail .head) (.tail (.tail (.tail .head)))
    | .onFalse => arm (.tail (.tail .head)) (.tail (.tail (.tail (.tail .head))))
  suffix := .load (.latest 0) (.arg (.tail .head))
    (.ret (.latest 0) (.output (0 : Fin 1) .head))

private def afterTrue : Heap 3 := (initial.write trueCell 7).write x 11
private def afterFalse : Heap 3 := (initial.write falseCell 7).write x 33

example : (diamond .onTrue).Returns true input initial 11 afterTrue :=
  ((diamond .onTrue).returns_iff_denote true input initial 11 afterTrue).mpr (by cbv)

example : (diamond .onTrue).Returns false input initial 33 afterFalse :=
  ((diamond .onTrue).returns_iff_denote false input initial 33 afterFalse).mpr (by cbv)

example : (diamond .onFalse).Returns true input initial 11 afterTrue :=
  ((diamond .onFalse).returns_iff_denote true input initial 11 afterTrue).mpr (by cbv)

example : (diamond .onFalse).Returns false input initial 33 afterFalse :=
  ((diamond .onFalse).returns_iff_denote false input initial 33 afterFalse).mpr (by cbv)

-- Reversing the predecessor order moves the true arm's heap to the second slot.
example : latch (diamond .onFalse).merge .second (publish .onTrue afterTrue) = some afterTrue := by cbv
example : latch (diamond .onFalse).merge .first (publish .onTrue afterTrue) = none := by cbv

-- Each taken arm saves the old x. The other arm's cell is untouched.
example (first : Projection) :
    ((diamond first).denote true input initial).2.read trueCell = 7 ∧
      ((diamond first).denote true input initial).2.read falseCell = 0 := by
  constructor <;> cbv

example (first : Projection) :
    ((diamond first).denote false input initial).2.read falseCell = 7 ∧
      ((diamond first).denote false input initial).2.read trueCell = 0 := by
  constructor <;> cbv

end Silmaril.SSA.SeaOfNodes.Memory.Diamond
