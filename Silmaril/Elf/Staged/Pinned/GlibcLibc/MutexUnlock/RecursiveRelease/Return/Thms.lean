module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Return.Defs
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ReleaseReturn

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Return

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.X86
open Silmaril.X86.Ext (Loaded leBytes)
open Silmaril.Machine.Execution (run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Process (Memory)

/-- A reached private depth-one release with two readable stack slots disjoint
from the mutex writes returns zero in seventeen Atomic9 steps. The frame
restores RBP and uses the incoming RBP for the modular stack-pointer update.
The release's four updated dwords and outside-memory frame persist through RET. -/
theorem private_release_return {initial : MState} {kind users : BitVec 32} {savedFrame target : Word}
    (entry : RecursiveRelease.Entry initial kind users)
    (aligned : (initial.core.read .rdi).toNat % 4 = 0)
    (lock : initial.memory.readBytes (initial.core.read .rdi).toNat 4 = some [1, 0, 0, 0])
    (writable : initial.memory.Permitted .write (initial.core.read .rdi).toNat 4)
    (compare : Loaded initial.memory 0xa1ba4 NoWakeReturn.compareBytes)
    (epilogue : Loaded initial.memory 0xa1b94 NoWakeReturn.returnBytes)
    (saved : initial.memory.readBytes (initial.core.read .rbp).toNat 8 = some (encodeWords [savedFrame]))
    (targetSlot : initial.memory.readBytes (initial.core.read .rbp + 8#64).toNat 8 =
      some (encodeWords [target]))
    (savedApart : StackSlotApart (initial.core.read .rdi).toNat (initial.core.read .rbp).toNat 8)
    (targetApart : StackSlotApart (initial.core.read .rdi).toNat (initial.core.read .rbp + 8#64).toNat 8) :
    ∃ final, run Atomic9.step 17 initial = some final ∧
      final.core.rip = target ∧ final.core.read .rax = 0#64 ∧
      final.core.read .rsp = initial.core.read .rbp + 16#64 ∧ final.core.read .rbp = savedFrame ∧
      initial.memory.WritesOnly final.memory (initial.core.read .rdi).toNat 16 ∧
      ∀ offset, offset < 4 →
        let base := (initial.core.read .rdi).toNat
        final.memory.bytes.get? (base + offset) = some 0 ∧
        final.memory.bytes.get? (base + 4 + offset) = some 0 ∧
        final.memory.bytes.get? (base + 8 + offset) = some 0 ∧
        final.memory.bytes.get? (base + 12 + offset) =
          (leBytes ((users - 1#32).setWidth 64) 4)[offset]? :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.ReleaseReturn.private_release_return
    entry aligned lock writable compare epilogue saved targetSlot savedApart targetApart

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveRelease.Return
