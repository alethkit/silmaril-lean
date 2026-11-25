module

public import Silmaril.Elf.Corpus.SqliteRead.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteRead.Destination.Frame

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteRead.Destination

open Silmaril.Elf.Corpus.SqliteRead
open Silmaril.Process
open Silmaril.X86 (MState Word)
open Silmaril.X86.Ext.Wire (Platform)

/-- The permission-checked read of the actual destination span is invariant
across the dispatch, as is write permission for that span. -/
theorem dispatch_destination_observation {platform : Platform}
    {initial reached : MState} {page : PageRead} {methods target : Word}
    (entry : Entry initial page methods target)
    (dispatched : Dispatches platform initial page.request target reached) :
    let request := argument reached.core
    reached.memory.readBytes request.buffer.toNat request.amount.toNat =
      initial.memory.readBytes request.buffer.toNat request.amount.toNat ∧
    (reached.memory.Permitted .write request.buffer.toNat request.amount.toNat ↔
      initial.memory.Permitted .write request.buffer.toNat request.amount.toNat) :=
  Silmaril.Proofs.Elf.Corpus.SqliteRead.Destination.dispatch_destination_observation entry dispatched

end Silmaril.Elf.Corpus.SqliteRead.Destination
