module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn.Defs

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Return

/-- The read span is disjoint from the four dwords written during release. -/
def StackSlotApart (mutex address size : Nat) : Prop :=
  address + size ≤ mutex ∨ mutex + 16 ≤ address

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Return
