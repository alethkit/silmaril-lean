module

public import Silmaril.Elf.Corpus.MimallocVersion.Source.Core.Defs
import Silmaril.Proofs.Elf.Corpus.MimallocVersion.SourceCore

@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocVersion.Source.Core

/-- Actual elaboration binds this source Ail to this Core procedure. -/
theorem elaborates : Task.elaborates :=
  Silmaril.Proofs.Elf.Corpus.MimallocVersion.SourceCore.elaborates

open Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21 in
/-- Canonical ELF bytes at the actual exported function's virtual address. -/
theorem canonical_code_at : Silmaril.Elf.CodeAt F 0xe2b0 codeO3 :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

end Silmaril.Elf.Corpus.MimallocVersion.Source.Core
