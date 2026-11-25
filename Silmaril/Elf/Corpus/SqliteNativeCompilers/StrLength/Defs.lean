module

public import Silmaril.X86.Open.Thms

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers.StrLength

open Silmaril.X86

/-- The GCC body of `sqlite3_str_length` starts by zeroing EAX, then skips the
load on null. -/
def gccCode : List Byte :=
  [0x31, 0xc0, 0x48, 0x85, 0xff, 0x74, 0x03, 0x8b, 0x47, 0x18, 0xc3]

/-- The Clang body of `sqlite3_str_length` branches to a separate zero-return
block on null. -/
def clangCode : List Byte :=
  [0x48, 0x85, 0xff, 0x74, 0x04, 0x8b, 0x47, 0x18, 0xc3, 0x31, 0xc0, 0xc3]

/-- A non-null pointer in RDI must permit a four-byte read of the common length
at offset 24. A null pointer requires no field read. -/
def FieldReadable (entry : MState) (length : BitVec 32) : Prop :=
  entry.core.read .rdi ≠ 0#64 →
    Ext.loadN entry.memory (entry.core.read .rdi + 24) 4 = some (length.setWidth 64)

end Silmaril.Elf.Corpus.SqliteNativeCompilers.StrLength
