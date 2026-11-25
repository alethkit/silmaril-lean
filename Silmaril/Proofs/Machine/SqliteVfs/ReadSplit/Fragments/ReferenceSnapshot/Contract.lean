module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Defs
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit (combine read_result_combine)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments (fragmentRequests readFragments read_fragments_trace)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot

private theorem combine_empty {bytes : Bytes} {offset count : Nat} {reply : ReadReply}
    (read : ReadResult bytes offset count reply) : combine (.ok []) reply = some reply := by
  obtain ⟨buffer, rfl, _⟩ := read
  split <;> rfl

/-- A schedule-specific proof of the individual responses suffices for the
aggregate byte contract. The trace ends at the returned state. -/
theorem read_fragments_snapshot_contract {State : Type} (step : Handler State)
    (snapshot : Bytes) (handle : Handle) (state : State) (offset count : Nat)
    (rest : List Nat) (reads : ReadsSnapshot step snapshot handle state offset (count :: rest)) :
    let result := readFragments step handle state offset count rest
    (∃ reply, result.reply = some reply ∧ ReadResult snapshot offset (count + rest.sum) reply) ∧
      Trace.Valid step state result.trace result.file ∧
      result.trace.map Exchange.request = fragmentRequests handle offset (count :: rest) := by
  refine ⟨?_, read_fragments_trace step handle state offset count rest⟩
  induction rest generalizing state offset count with
  | nil =>
    exact ⟨(step state (.read handle offset count)).1, combine_empty reads.1,
      by simpa only [List.sum_nil, Nat.add_zero] using reads.1⟩
  | cons next rest ih =>
    let first := step state (.read handle offset count)
    obtain ⟨tailReply, tailResult, tailRead⟩ := ih first.2 (offset + count) next reads.2
    obtain ⟨reply, combined, combinedRead⟩ := read_result_combine reads.1 tailRead
    refine ⟨reply, ?_, combinedRead⟩
    change
      (readFragments step handle first.2 (offset + count) next rest).reply.bind
        (combine first.1) = some reply
    rw [tailResult]
    exact combined

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot
