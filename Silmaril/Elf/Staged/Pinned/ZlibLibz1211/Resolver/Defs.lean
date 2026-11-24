module

public import Silmaril.Elf.Facts.Defs

/-! # The pinned Ubuntu zlib 1.2.11 `crc32_z` resolver -/

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.ZlibLibz1211

open Silmaril.Elf

/-- The strong reference to `crc32_z` at version `ZLIB_1.2.9`. -/
def crc32zSelector : Sel :=
  .dyn ⟨nameOf "crc32_z", false, some ⟨nameOf "ZLIB_1.2.9", 136832457, false⟩⟩

/-- The `STT_GNU_IFUNC` entry in `.dynsym` names the resolver's address and size. -/
def crc32zResolver : Def :=
  { index := 25, value := 0x75e0, size := 12, ifunc := true, abs := false }

/-- The bytes at file offset `0x75e0` in `examples/elf/pinned/zlib-libz.so.1.2.11`. -/
def crc32zResolverBytes : List (BitVec 8) :=
  [0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8d, 0x05, 0x05, 0xae, 0xff, 0xff, 0xc3]

end Silmaril.Elf.Staged.Pinned.ZlibLibz1211
