module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Defs
public import Silmaril.X86.Atomic9.Defs
public import Silmaril.Machine.Execution

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue

open Silmaril.X86 (Byte)

/-- The pinned unlock entry through the branch to recursive dispatch. -/
def codeBytes : List Byte :=
  [0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x47, 0x10, 0x89, 0xc2,
   0x81, 0xe2, 0x7f, 0x01, 0x00, 0x00, 0xa8, 0x7c, 0x75, 0x5d,
   0x55, 0x48, 0x89, 0xe5, 0x48, 0x83, 0xec, 0x10, 0x85, 0xd2, 0x75, 0x61]

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursivePrologue
