module

public import Silmaril.Elf.Corpus.SqliteRead.Defs
import Silmaril.Process.Memory
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteRead.Destination

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
      initial.memory.Permitted .write request.buffer.toNat request.amount.toNat) := by
  dsimp only
  rw [dispatched.request]
  have frame := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp dispatched.frame
  refine ⟨frame.readBytes ?_, frame.permitted_iff .write _ _⟩
  intro offset within
  change offset < page.count.toNat at within
  change ¬ (stackSlot initial ≤ page.buffer.toNat + offset ∧
    page.buffer.toNat + offset < stackSlot initial + 8)
  rcases entry.stackApart with left | right <;> omega

end Silmaril.Proofs.Elf.Corpus.SqliteRead.Destination
