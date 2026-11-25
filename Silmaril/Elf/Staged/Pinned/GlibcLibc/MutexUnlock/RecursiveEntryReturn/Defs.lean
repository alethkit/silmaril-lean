module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Return.Defs

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveEntryReturn

open Silmaril.X86
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Machine.LittleEndian (encodeWords)

def savedSlot (initial : MState) : Word := initial.core.read .rsp - 8#64

def SavedApart (initial : MState) (address size : Nat) : Prop :=
  address + size ≤ (savedSlot initial).toNat ∨ (savedSlot initial).toNat + 8 ≤ address

/-- The later release premises on the entry memory and RDI. The instruction
pointer in the real execution is established separately by the prefix. -/
def ReleaseMemory (initial : MState) (users : BitVec 32) : Prop :=
  RecursiveRelease.Entry {initial with core := {initial.core with rip := 0xa1c06}} 1 users

/-- Mapped private recursive unlock at the versioned symbol's link-time entry.
The saved-frame write is separated from the later reads and the mutex fields. -/
structure Entry (initial : MState) (threadId users : BitVec 32) (target : Word) : Prop where
  rip : initial.core.rip = 0xa1b50
  entry : Loaded initial.memory 0xa1b50 RecursivePrologue.codeBytes
  dispatch : Loaded initial.memory 0xa1bd0 RecursiveDispatch.dispatchBytes
  recursive : Loaded initial.memory 0xa1be7 RecursiveDispatch.recursiveBytes
  ownerCode : Loaded initial.memory 0xa1bf2 OwnerCheck.ownerBytes
  thread : loadN initial.memory (initial.core.fsBase + 0x2d0#64) 4 = some (threadId.setWidth 64)
  owner : loadN initial.memory (initial.core.read .rdi + 8#64) 4 = some (threadId.setWidth 64)
  release : ReleaseMemory initial users
  aligned : (initial.core.read .rdi).toNat % 4 = 0
  lock : initial.memory.readBytes (initial.core.read .rdi).toNat 4 = some [1, 0, 0, 0]
  lockWrite : initial.memory.Permitted .write (initial.core.read .rdi).toNat 4
  compare : Loaded initial.memory 0xa1ba4 NoWakeReturn.compareBytes
  epilogue : Loaded initial.memory 0xa1b94 NoWakeReturn.returnBytes
  savedWrite : initial.memory.Permitted .write (savedSlot initial).toNat 8
  savedRead : initial.memory.Permitted .read (savedSlot initial).toNat 8
  targetSlot : initial.memory.readBytes (initial.core.read .rsp).toNat 8 = some (encodeWords [target])
  codeApart : SavedApart initial 0xa1b50 (0xa1c10 - 0xa1b50)
  mutexApart : SavedApart initial (initial.core.read .rdi).toNat 20
  threadApart : SavedApart initial (initial.core.fsBase + 0x2d0#64).toNat 4
  flagApart : SavedApart initial 0x20c040 1
  savedTargetApart : SavedApart initial (initial.core.read .rsp).toNat 8
  targetMutexApart : RecursiveRelease.Return.StackSlotApart
      (initial.core.read .rdi).toNat (initial.core.read .rsp).toNat 8

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveEntryReturn
