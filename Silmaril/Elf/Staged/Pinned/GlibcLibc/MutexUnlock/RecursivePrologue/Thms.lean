module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue

open Silmaril.Elf
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.X86
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Machine.Execution (run)
open Silmaril.Machine.LittleEndian (encodeWords)

/-- The span starts at the pinned versioned unlock symbol's entry. -/
theorem code :
    CodeAt F 0xa1b50 codeBytes ∧ MutexUnlock.entry.value = 0xa1b50 ∧
      codeBytes.length ≤ MutexUnlock.entry.size :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue.code

/-- A readable kind dword of one selects recursive dispatch after eleven
Atomic9 steps. Frame construction writes exactly the saved-RBP slot.
The two stack-pointer subtractions use 64-bit arithmetic. -/
theorem recursive_prologue {initial : MState}
    (rip : initial.core.rip = 0xa1b50)
    (loaded : Loaded initial.memory 0xa1b50 codeBytes)
    (kind : loadN initial.memory (initial.core.read .rdi + 16#64) 4 = some 1#64)
    (writable : initial.memory.Permitted .write (initial.core.read .rsp - 8#64).toNat 8)
    (apart : (initial.core.read .rsp - 8#64).toNat + 8 ≤ 0xa1b50 ∨
      0xa1b6f ≤ (initial.core.read .rsp - 8#64).toNat) :
    ∃ final, run Atomic9.step 11 initial = some final ∧ final.core.rip = 0xa1bd0 ∧
      final.core.read .rax = 1 ∧ final.core.read .rdx = 1 ∧
      final.core.read .rbp = initial.core.read .rsp - 8#64 ∧
      final.core.read .rsp = initial.core.read .rsp - 8#64 - 16#64 ∧
      (∀ reg, reg ≠ .rax → reg ≠ .rdx → reg ≠ .rsp → reg ≠ .rbp →
        final.core.read reg = initial.core.read reg) ∧ final.core.fsBase = initial.core.fsBase ∧
      initial.memory.writeBytes (initial.core.read .rsp - 8#64).toNat
        (encodeWords [initial.core.read .rbp]) = some final.memory ∧
      initial.memory.WritesOnly final.memory (initial.core.read .rsp - 8#64).toNat 8 :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue.recursive_prologue
    rip loaded kind writable apart

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue
