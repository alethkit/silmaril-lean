module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Defs
public import Silmaril.X86.Atomic9.Defs
public import Silmaril.Machine.Execution

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch

open Silmaril.X86 (Byte)

def dispatchBytes : List Byte := [0x81, 0xfa, 0, 1, 0, 0, 0x75, 0x0f]
def recursiveBytes : List Byte := [0x8b, 0x47, 0x10, 0x83, 0xe0, 0x7f, 0x83, 0xf8, 1, 0x75, 0x22]

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveDispatch
