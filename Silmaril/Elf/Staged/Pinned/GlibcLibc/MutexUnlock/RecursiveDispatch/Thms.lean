module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch

open Silmaril.Elf
open Silmaril.Elf.Staged.Pinned.GlibcLibc
open Silmaril.X86
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Machine.Execution (run)

/-- Both spans occur inside the pinned versioned unlock symbol. -/
theorem code :
    CodeAt F 0xa1bd0 dispatchBytes ∧ CodeAt F 0xa1be7 recursiveBytes ∧
      MutexUnlock.entry.value ≤ 0xa1bd0 ∧
      0xa1be7 + recursiveBytes.length ≤ MutexUnlock.entry.value + MutexUnlock.entry.size :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch.code

/-- From reached recursive dispatch with RDX=1 and a readable kind dword of
one, six steps reach the owner check. RAX contains the masked kind. Other
general registers, FS base and memory are unchanged. -/
theorem recursive_dispatch {initial : MState}
    (rip : initial.core.rip = 0xa1bd0)
    (edx : initial.core.read .rdx = 1#64)
    (dispatch : Loaded initial.memory 0xa1bd0 dispatchBytes)
    (recursive : Loaded initial.memory 0xa1be7 recursiveBytes)
    (kind : loadN initial.memory (initial.core.read .rdi + 16#64) 4 = some 1#64) :
    ∃ final, run Atomic9.step 6 initial = some final ∧ final.core.rip = 0xa1bf2 ∧
      final.core.read .rax = 1#64 ∧
      (∀ reg, reg ≠ .rax → final.core.read reg = initial.core.read reg) ∧
      final.core.fsBase = initial.core.fsBase ∧ final.memory = initial.memory :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch.recursive_dispatch
    rip edx dispatch recursive kind

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch
