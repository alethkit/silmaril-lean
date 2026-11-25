module

public import Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteMutex.Unlock.SlotTable

public section

namespace Silmaril.Elf.Corpus.SqliteMutex.Unlock.SlotTable

open Silmaril.Elf.Link
open Silmaril.Elf.Link.DynElf
open Silmaril.X86.Link (Blob)

local notation "Sqlite" => Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F

/-- The current all-slot construction fails for the pinned SQLite file.
The regular relocation table contains a record with no modeled value. -/
theorem no_sqlite_slot_table (resolver : Dyn.Resolver) (lazy : Bool) (dynamic : Elf.DynInfo)
    (headers : Dyn.finfo Sqlite = some dynamic) :
    Dyn.slotsWith resolver lazy Sqlite dynamic = none :=
  Proofs.Elf.Corpus.SqliteMutex.Unlock.SlotTable.no_sqlite_slot_table resolver lazy dynamic headers

/-- The current head-image relation cannot describe the pinned SQLite file
as the first object in the modeled lookup scope. -/
theorem sqlite_cannot_head_exe_loaded (scopeTail : List Blob) (bases : List Silmaril.X86.Word)
    (ifunc : Silmaril.X86.Word → Option Silmaril.X86.Word) (lazy : Bool)
    (resolver : Silmaril.X86.Word) (memory : Silmaril.Process.Memory) :
    ¬ Dyn.ExeLoaded (Sqlite :: scopeTail) bases ifunc lazy resolver memory :=
  Proofs.Elf.Corpus.SqliteMutex.Unlock.SlotTable.sqlite_cannot_head_exe_loaded scopeTail bases ifunc lazy resolver memory

end Silmaril.Elf.Corpus.SqliteMutex.Unlock.SlotTable
