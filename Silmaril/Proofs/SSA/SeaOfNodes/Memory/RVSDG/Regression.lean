module

import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory

open RVSDG (Origin Tuple)
open RVSDG.OrderedRuntime.Structured (EntryChecked Threaded runtimePort)

private abbrev args : List ValueSort := [.address, .word, .word]

private def address {past : List (List ValueSort)} : Origin args past .address :=
  .arg .head

private def firstWord {past : List (List ValueSort)} : Origin args past .word :=
  .arg (.tail .head)

private def secondWord {past : List (List ValueSort)} : Origin args past .word :=
  .arg (.tail (.tail .head))

-- A straight-line instance of Simple chapter 10's read-before-overwrite case.
-- The later load adds a local, but the return still selects the earlier one.
-- https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/test/java/com/seaofnodes/simple/Chapter10Test.java#L488-L501
private def readBeforeOverwrite : Graph args :=
  .store (.latest 0) address firstWord
    (.load (.latest 1) address
      (.store (.latest 1) address secondWord
        (.load (.latest 2) address
          (.ret (.latest 2) (.output (1 : Fin 2) .head)))))

private def x : Address 2 := 0
private def y : Address 2 := 1
private def initial : Heap 2 := fun _ => 7
private def input : Tuple (Val 2) args := .cons x (.cons (11 : Word) (.cons (33 : Word) .nil))

private def final : Heap 2 := (initial.write x 11).write x 33

example : EntryChecked (inputData args) wordData readBeforeOverwrite.lower.toTerm :=
  readBeforeOverwrite.lowerChecked

example : readBeforeOverwrite.lower.run (leafModel 2).toRVSDG (encodeInput initial input) =
    encodeResult 11 final := by rfl

example : readBeforeOverwrite.Returns input initial 11 final :=
  (readBeforeOverwrite.lower_returns_iff input initial 11 final).mpr (by rfl)

private def result : Tuple (WireVal 2) (Threaded wordPorts) :=
  readBeforeOverwrite.lower.run (leafModel 2).toRVSDG (encodeInput initial input)

example : result.get .head = (11 : Word) := by rfl
example : Heap.read (result.get (runtimePort wordPorts)) x = 33 := by rfl
example : Heap.read (result.get (runtimePort wordPorts)) y = 7 := by rfl

end Silmaril.SSA.SeaOfNodes.Memory
