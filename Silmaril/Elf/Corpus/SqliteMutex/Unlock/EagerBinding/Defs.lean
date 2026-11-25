module

public import Silmaril.Elf.Corpus.SqliteMutex.Unlock.Defs
public import Silmaril.Elf.Link.Dyn.Loader.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.Bytes
public import Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.Bytes

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding

open Silmaril.Elf
open Silmaril.Elf.Link
open Silmaril.Elf.Link.DynElf
open Silmaril.Elf.Corpus.SqliteMutex.Unlock
open Silmaril.X86.Link (Blob)
open Silmaril.X86 (Word)

local notation "Sqlite" => Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F
local notation "Glibc" => Silmaril.Elf.Staged.Pinned.GlibcLibc.F

/-- Supplied model scope with the two pinned objects first in search order. -/
noncomputable def scope (tail : List Blob) : List Blob := Sqlite :: Glibc :: tail

/-- The plain, relative definition in the pinned glibc object. -/
def glibcDefinition : DynElf.Elf.Def := ⟨0xa1b50, false, false⟩

/-- The absolute symbol relocation at index 1170 in the SQLite DT_RELA table. -/
def absoluteReloc : Elf.Rela := ⟨0x10e520, 1, 195, 0⟩

/-- Read the indexed relocation through the dynamic tags. -/
def readAbsoluteReloc : Rd Elf.Rela := do
  let info ← Elf.dynInfo
  let table ← Rd.ofOption (info.tagOff Elf.DT_RELA)
  Rd.guard (1170 < ((info.tag Elf.DT_RELASZ).getD 0 / 24))
  Elf.rela (table + 24 * 1170)

end Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding
