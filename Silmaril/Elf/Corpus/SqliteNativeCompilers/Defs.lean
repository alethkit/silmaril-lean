module

public import Silmaril.X86.Open.Thms

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers

open Silmaril.X86 (Byte)

/-- The six bytes of `sqlite3_libversion_number` emitted by both pinned compilers:
`mov $3054001, %eax; ret`. -/
def libversionNumberCode : List Byte := [0xb8, 0xb1, 0x99, 0x2e, 0x00, 0xc3]

end Silmaril.Elf.Corpus.SqliteNativeCompilers
