module

public import Silmaril.Elf.Corpus.SqliteNativeCompilers.StrLength.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.StrLength.Run

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers.StrLength

open Silmaril.X86

/-- The two loaded symbol bodies first-return zero for null pointers and the common
32-bit length for non-null pointers. Each preserves its own entire memory. -/
theorem strLength_pair {gcc clang : MState} {gccBase clangBase : Word}
    {length : BitVec 32}
    (gccLoaded : Ext.Loaded gcc.memory gccBase gccCode)
    (clangLoaded : Ext.Loaded clang.memory clangBase clangCode)
    (gccEntry : gcc.core.rip = gccBase) (clangEntry : clang.core.rip = clangBase)
    (gccAbi : FnContract.AbiEntry gcc.core gcc.memory)
    (clangAbi : FnContract.AbiEntry clang.core clang.memory)
    (sameNull : gcc.core.read .rdi = 0#64 ↔ clang.core.read .rdi = 0#64)
    (gccField : FieldReadable gcc length)
    (clangField : FieldReadable clang length) :
    ∃ gccFinal clangFinal, FnContract.FirstReturn Open.isa gcc gccFinal ∧
      FnContract.FirstReturn Open.isa clang clangFinal ∧
      gccFinal.core.read .rax = (if gcc.core.read .rdi = 0#64 then 0 else length.setWidth 64) ∧
      clangFinal.core.read .rax = gccFinal.core.read .rax ∧
      gccFinal.memory = gcc.memory ∧ clangFinal.memory = clang.memory :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.StrLength.strLength_pair
    gccLoaded clangLoaded gccEntry clangEntry gccAbi clangAbi sameNull gccField clangField

end Silmaril.Elf.Corpus.SqliteNativeCompilers.StrLength
