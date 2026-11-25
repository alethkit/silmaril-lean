module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn

open Silmaril.Elf
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.X86
open Silmaril.X86.Ext (Loaded)
open Silmaril.Machine.Execution (run)
open Silmaril.Machine.LittleEndian (encodeWords)

/-- Both spans are the pinned bytes inside the versioned unlock symbol. -/
theorem code :
    CodeAt F 0xa1ba4 compareBytes ∧ CodeAt F 0xa1b94 returnBytes ∧
      MutexUnlock.entry.value ≤ 0xa1b94 ∧
      0xa1ba4 + compareBytes.length ≤ MutexUnlock.entry.value + MutexUnlock.entry.size :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn.code

/-- Starting at the wake test with RAX equal to one, the signed branch skips
the wake call. The epilogue restores RBP, pops the return target and returns zero.
The stack addresses and updated RSP use 64-bit arithmetic. -/
theorem no_wake_return {initial : MState} {savedFrame target : Word}
    (rip : initial.core.rip = 0xa1ba4)
    (old : initial.core.read .rax = 1#64)
    (compareLoaded : Loaded initial.memory 0xa1ba4 compareBytes)
    (returnLoaded : Loaded initial.memory 0xa1b94 returnBytes)
    (saved : initial.memory.readBytes (initial.core.read .rbp).toNat 8 =
      some (encodeWords [savedFrame]))
    (returnSlot : initial.memory.readBytes (initial.core.read .rbp + 8#64).toNat 8 =
      some (encodeWords [target])) :
    ∃ final, run Atomic9.step 6 initial = some final ∧
      final.core.rip = target ∧ final.core.read .rax = 0#64 ∧
      final.core.read .rsp = initial.core.read .rbp + 16#64 ∧
      final.core.read .rbp = savedFrame ∧
      (∀ reg, reg ≠ .rax → reg ≠ .rsp → reg ≠ .rbp →
        final.core.read reg = initial.core.read reg) ∧
      final.memory = initial.memory :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn.no_wake_return
    rip old compareLoaded returnLoaded saved returnSlot

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn
