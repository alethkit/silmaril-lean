module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck

open Silmaril.Elf
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.X86
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Machine.Execution (run)

/-- The listed bytes occur inside the pinned versioned unlock symbol. -/
theorem code :
    CodeAt F 0xa1bf2 ownerBytes ∧
      MutexUnlock.entry.value ≤ 0xa1bf2 ∧
      0xa1bf2 + ownerBytes.length ≤ MutexUnlock.entry.value + MutexUnlock.entry.size :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck.code

/-- Three Atomic9 steps compare the FS-relative dword to the mutex owner.
Equality reaches the depth decrement. Inequality reaches the error epilogue.
No stack or mutex bytes change during this cut. -/
theorem owner_check {initial : MState} {threadId owner : BitVec 32}
    (rip : initial.core.rip = 0xa1bf2)
    (loaded : Loaded initial.memory 0xa1bf2 ownerBytes)
    (threadRead : loadN initial.memory (initial.core.fsBase + 0x2d0#64) 4 =
      some (threadId.setWidth 64))
    (ownerRead : loadN initial.memory (initial.core.read .rdi + 8#64) 4 =
      some (owner.setWidth 64)) :
    ∃ final, run Atomic9.step 3 initial = some final ∧
      final.core.rip = (if owner = threadId then 0xa1c06 else 0xa1bff) ∧
      final.core.read .rax = threadId.setWidth 64 ∧
      (∀ reg, reg ≠ .rax → final.core.read reg = initial.core.read reg) ∧
      final.core.fsBase = initial.core.fsBase ∧ final.memory = initial.memory :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck.owner_check
    rip loaded threadRead ownerRead

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck
