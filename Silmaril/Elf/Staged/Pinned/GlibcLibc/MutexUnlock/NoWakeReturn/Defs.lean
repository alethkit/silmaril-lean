module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Defs
public import Silmaril.X86.Atomic9.Defs
public import Silmaril.Machine.Execution

/-! The wake test and return epilogue of the pinned glibc mutex unlock.
These byte spans use link-time virtual addresses. -/

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn

open Silmaril.X86 (Byte)

def compareBytes : List Byte := [0x83, 0xf8, 0x01, 0x7e, 0xeb]
def returnBytes : List Byte := [0x90, 0x31, 0xc0, 0xc9, 0xc3]

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.NoWakeReturn
