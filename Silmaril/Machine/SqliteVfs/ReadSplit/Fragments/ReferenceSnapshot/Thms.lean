module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Contract

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot

open Silmaril.Machine.SqliteVfs

/-- A schedule-specific proof of the individual responses suffices for the
aggregate byte contract. The trace ends at the returned state. -/
theorem read_fragments_snapshot_contract {State : Type} (step : Handler State)
    (snapshot : Bytes) (handle : Handle) (state : State) (offset count : Nat)
    (rest : List Nat) (reads : ReadsSnapshot step snapshot handle state offset (count :: rest)) :
    let result := readFragments step handle state offset count rest
    (∃ reply, result.reply = some reply ∧ ReadResult snapshot offset (count + rest.sum) reply) ∧
      Trace.Valid step state result.trace result.file ∧
      result.trace.map Exchange.request = fragmentRequests handle offset (count :: rest) :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.read_fragments_snapshot_contract
    step snapshot handle state offset count rest reads

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot
