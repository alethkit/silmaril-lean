module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Defs

/-! # Delete a common Store overwritten on both occurrences -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore

open RVSDG (Port Tuple)
open SeaOfNodes.Diamond (Slot)

variable {args : List ValueSort} {cells : Nat}

structure PrefixStore (args : List ValueSort) where
  address : Port args .address
  value : Port args .word

/-- Execute the entry Store in the native memory model. Its boundary exports
the memory version that enters the diamond. -/
def PrefixStore.table (store : PrefixStore args) : Memory.Graph args :=
  .store (.latest 0) (.arg store.address) (.arg store.value) (.ret (.latest 1) (.arg store.value))

/-- Form the native straight-line table for the entry Store followed by one arm. -/
def PrefixStore.prepend (store : PrefixStore args) (arm : Memory.Graph args) : Memory.Graph args :=
  .store (.latest 0) (.arg store.address) (.arg store.value) (Memory.DeadStore.reindexMemory arm 1)

/-- One entry Store and an ordinary memory diamond with an evaluated guard. -/
structure Prefixed (args : List ValueSort) where
  store : PrefixStore args
  diamond : Graph args

def Prefixed.Returns (source : Prefixed args) (guard : Bool) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) : Prop :=
  ∃ entryWord entryHeap, source.store.table.Returns input initial entryWord entryHeap ∧
    source.diamond.Returns guard input entryHeap word final

def Prefixed.denote (source : Prefixed args) (guard : Bool) (input : Tuple (Val cells) args)
    (initial : Heap cells) : Word × Heap cells :=
  source.diamond.denote guard input (source.store.table.denote input initial).2

structure ArmOverwrite (args : List ValueSort) where
  /-- The one-based Store version within this original arm. -/
  storeVersion : Nat
  readers : List (Port args .address)

/-- Each Region input occurrence has its own overwrite and reader evidence. -/
abbrev Candidate (args : List ValueSort) := Slot → ArmOverwrite args

def rewriteSlot (source : Prefixed args) (candidate : Candidate args) (input : Tuple (Val cells) args)
    (arrival : Slot) : Option (Memory.Graph args) :=
  let witness := candidate arrival
  let arm := source.diamond.arm (source.diamond.merge.predecessor arrival)
  Memory.DeadStore.rewrite (source.store.prepend arm) ⟨1, witness.storeVersion + 1⟩
    ⟨source.store.address, witness.readers⟩ input

/-- Require the checked deletion on both Region occurrences. The target
has no entry Store and runs the selected rewritten arm and original suffix. -/
def rewrite (source : Prefixed args) (candidate : Candidate args) (input : Tuple (Val cells) args) :
    Option (Graph args) := do
  let first ← rewriteSlot source candidate input .first
  let second ← rewriteSlot source candidate input .second
  some { source.diamond with
    arm := fun edge => match source.diamond.merge.slot edge with
      | .first => first
      | .second => second }

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore
