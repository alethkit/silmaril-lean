module

import Silmaril.SSA.SeaOfNodes.Memory.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory

open RVSDG (Origin Tuple)

private abbrev args : List ValueSort := [.address, .address, .word, .word]

private def firstAddress {past : List (List ValueSort)} : Origin args past .address :=
  .arg .head

private def secondAddress {past : List (List ValueSort)} : Origin args past .address :=
  .arg (.tail .head)

private def firstWord {past : List (List ValueSort)} : Origin args past .word :=
  .arg (.tail (.tail .head))

private def secondWord {past : List (List ValueSort)} : Origin args past .word :=
  .arg (.tail (.tail (.tail .head)))

private def x : Address 2 := 0
private def y : Address 2 := 1
private def initial : Heap 2 := fun _ => 0

private def input (other : Address 2) (a b : Word) : Tuple (Val 2) args :=
  .cons x (.cons other (.cons a (.cons b .nil)))

-- Chapter 10's Point example after allocation and field initialization.
-- The load of x still takes the memory edge from the intervening store to y.
-- https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#one-memory-value
private def point : Graph args :=
  .store (.latest 0) firstAddress firstWord
    (.store (.latest 1) secondAddress secondWord
      (.load (.latest 2) firstAddress
        (.ret (.latest 2) (.output (0 : Fin 1) .head))))

private def pointFinal : Heap 2 := (initial.write x 3).write y 42

example : point.Returns (input y 3 42) initial 3 pointFinal :=
  (point.returns_iff_denote (input y 3 42) initial 3 pointFinal).mpr (by cbv)

example : ((point.denote (input y 3 42) initial).2).read y = 42 := by cbv

-- When the addresses coincide, the same graph instead reads the second write.
example : (point.denote (input x 3 42) initial).1 = 42 := by cbv

-- A straight-line version of the read-before-overwrite dependency.
-- https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/test/java/com/seaofnodes/simple/Chapter10Test.java#L488-L501
private def readBeforeOverwrite : Graph args :=
  .store (.latest 0) firstAddress firstWord
    (.load (.latest 1) firstAddress
      (.store (.latest 1) firstAddress secondWord
        (.ret (.latest 2) (.output (0 : Fin 1) .head))))

private def overwritten : Heap 2 := (initial.write x 11).write x 33

example : readBeforeOverwrite.Returns (input y 11 33) initial 11 overwritten :=
  (readBeforeOverwrite.returns_iff_denote (input y 11 33) initial 11 overwritten).mpr (by cbv)

example : ((readBeforeOverwrite.denote (input y 11 33) initial).2).read x = 33 := by cbv

-- Start's memory wire is stale after one Store.
example (edge : MemoryInput 1) : edge.producer ≠ (0 : Fin 2) := by
  rw [edge.current]
  decide

end Silmaril.SSA.SeaOfNodes.Memory
