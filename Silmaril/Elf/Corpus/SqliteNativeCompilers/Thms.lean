module

public import Silmaril.Elf.Corpus.SqliteNativeCompilers.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.LibversionNumber

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers

open Silmaril.X86

/-- At any entry address with the checked slice loaded and a System V ABI entry, the first
return sets RAX to SQLite's version number, preserves the ABI return obligations, and leaves
memory unchanged. -/
theorem libversionNumber_firstReturn {entry : MState} {base : Word}
    (loaded : Ext.Loaded entry.memory base libversionNumberCode)
    (atEntry : entry.core.rip = base)
    (abi : FnContract.AbiEntry entry.core entry.memory) :
    ∃ final, FnContract.FirstReturn Open.isa entry final ∧
      FnContract.AbiReturn entry.core entry.memory final.core ∧
      final.core.read .rax = 3054001 ∧ final.memory = entry.memory :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.libversionNumber_firstReturn loaded atEntry abi

/-- The GCC and Clang slices have equal RAX at their respective first returns. Each preserves
its own input memory. The entry addresses, cores and memories may differ. -/
theorem libversionNumber_pair {gcc clang : MState} {gccBase clangBase : Word}
    (gccLoaded : Ext.Loaded gcc.memory gccBase libversionNumberCode)
    (clangLoaded : Ext.Loaded clang.memory clangBase libversionNumberCode)
    (gccEntry : gcc.core.rip = gccBase) (clangEntry : clang.core.rip = clangBase)
    (gccAbi : FnContract.AbiEntry gcc.core gcc.memory)
    (clangAbi : FnContract.AbiEntry clang.core clang.memory) :
    ∃ gccFinal clangFinal, FnContract.FirstReturn Open.isa gcc gccFinal ∧
      FnContract.FirstReturn Open.isa clang clangFinal ∧
      gccFinal.core.read .rax = clangFinal.core.read .rax ∧
      gccFinal.memory = gcc.memory ∧ clangFinal.memory = clang.memory := by
  obtain ⟨g, gr, _, gv, gm⟩ := libversionNumber_firstReturn gccLoaded gccEntry gccAbi
  obtain ⟨c, cr, _, cv, cm⟩ := libversionNumber_firstReturn clangLoaded clangEntry clangAbi
  exact ⟨g, c, gr, cr, gv.trans cv.symm, gm, cm⟩

end Silmaril.Elf.Corpus.SqliteNativeCompilers
