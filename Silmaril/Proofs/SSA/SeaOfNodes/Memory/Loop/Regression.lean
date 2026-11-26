module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Fixture

open RVSDG (Origin Tuple)

abbrev args : List ValueSort := [.address, .address, .word]

def headCell : Address 3 := 0
def tailCell : Address 3 := 1
def untouched : Address 3 := 2

def input : Tuple (Val 3) args :=
  .cons headCell (.cons tailCell (.cons (0 : Word) .nil))

def headWire {past : List (List ValueSort)} : Origin args past .address := .arg .head
def tailWire {past : List (List ValueSort)} : Origin args past .address := .arg (.tail .head)

def bodyTable : Memory.Graph args :=
  let oldTail : Origin args [[.word], [.word]] .word := .output (0 : Fin 2) .head
  let oldHead : Origin args [[.word], [.word]] .word := .output (1 : Fin 2) .head
  .load (.latest 0) headWire
    (.load (.latest 0) tailWire
      (.store (.latest 0) headWire oldTail
        (.store (.latest 1) tailWire (.arg (.tail (.tail .head)))
          (.ret (.latest 2) oldHead))))

-- Simple chapter 10 closes the loop's whole-memory Phi with its last Store.
-- Here a tail test checks the old head after the two stores have executed.
-- https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable
def shift : Graph args :=
  ⟨bodyTable, rfl, .tail (.tail .head)⟩

def initial (head : Word) : Heap 3 := fun address =>
  if address = headCell then head else if address = tailCell then 2 else 99

def update (heap : Heap 3) (newHead : Word) : Heap 3 :=
  (heap.write headCell newHead).write tailCell 0

def afterEntry : Heap 3 := update (initial 1) 2
def afterBackedge : Heap 3 := update afterEntry 0
def atExit : Heap 3 := update afterBackedge 0

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Fixture

end

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop

open Fixture

-- The first activation both copies the tail to the head and clears the tail,
-- even when it exits without a backedge.
example : shift.ReturnsAfter input (initial 0) 0 0 (update (initial 0) 2) :=
  (shift.returnsAfter_iff_evalAfter input (initial 0) 0 0 (update (initial 0) 2)).mpr (by cbv)

example : ((shift.evalAfter input (initial 0) 0).map fun result => result.2.read headCell) =
    some 2 := by cbv

-- The entry activation reads 1, but the first backedge activation reads 2
-- from the preceding Store to the same address.
example : bodyTable.Returns input (latch (initial 1) .entry PUnit.unit) 1 afterEntry :=
  (bodyTable.returns_iff_denote input (initial 1) 1 afterEntry).mpr (by cbv)

example : bodyTable.Returns input (latch (initial 1) .backedge afterEntry) 2 afterBackedge :=
  (bodyTable.returns_iff_denote input afterEntry 2 afterBackedge).mpr (by cbv)

example : shift.evalAfter input (initial 1) 1 = none := by cbv
example : shift.evalAfter input (initial 1) 3 = none := by cbv

private theorem counted : shift.ReturnsAfter input (initial 1) 2 0 atExit :=
  (shift.returnsAfter_iff_evalAfter input (initial 1) 2 0 atExit).mpr (by cbv)

example : (0, atExit) ∈ shift.denote input (initial 1) :=
  (shift.returns_iff_mem_denote input (initial 1) 0 atExit).mp ⟨2, counted⟩

example : atExit.read untouched = 99 := by cbv

end Silmaril.SSA.SeaOfNodes.Memory.Loop
