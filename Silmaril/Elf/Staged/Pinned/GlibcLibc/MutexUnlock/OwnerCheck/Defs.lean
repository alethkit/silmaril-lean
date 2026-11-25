module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Defs
public import Silmaril.X86.Atomic9.Defs
public import Silmaril.Machine.Execution

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck

open Silmaril.X86 (Byte)

/-- The FS-relative thread ID load, owner comparison and conditional branch. -/
def ownerBytes : List Byte := [0x64, 0x8b, 0x04, 0x25, 0xd0, 0x02, 0, 0, 0x39, 0x47, 0x08, 0x74, 0x07]

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.OwnerCheck
