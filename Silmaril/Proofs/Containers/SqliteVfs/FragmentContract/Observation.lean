module

public import Silmaril.Containers.SqliteVfs.FragmentContract.Defs
public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Defs
import Silmaril.Containers.SqliteVfs.Completed.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Thms

@[expose] public section

namespace Silmaril.Proofs.Containers.SqliteVfs.FragmentContract

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.FragmentContract (ReplyMatchesSnapshot)
open Silmaril.Containers.SqliteVfs.Completed (completed_exec_iff)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction (read_fragments_reconstruct)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot
  (ReadsSnapshot read_fragments_snapshot_contract)

private theorem readsSnapshot_of_trace {State : Type} {handler : Handler State}
    {start finish : State} {trace : Trace} (snapshot : Bytes) (handle : Handle)
    (offset : Nat) (counts : List Nat) (valid : Trace.Valid handler start trace finish)
    (requests : trace.map Exchange.request = fragmentRequests handle offset counts)
    (replies : ∀ e ∈ trace, ReplyMatchesSnapshot snapshot e) :
    ReadsSnapshot handler snapshot handle start offset counts := by
  induction counts generalizing start finish offset trace with
  | nil => exact trivial
  | cons count rest ih =>
    cases valid with
    | nil => simp [fragmentRequests] at requests
    | @cons before middle final request reply tail run validTail =>
      obtain ⟨rfl, orderedTail⟩ := List.cons.inj requests
      have read : ReadResult snapshot offset count reply := by
        have checked := replies ⟨.read handle offset count, reply⟩ (by simp)
        simpa only [Int.toNat_natCast] using checked.2.2
      have readTail := ih (offset + count) validTail orderedTail
        (fun e member => replies e (List.mem_cons_of_mem _ member))
      rw [ReadsSnapshot, run]
      exact ⟨read, readTail⟩

/-- A valid observation of the exact ordered requests determines the
contract on each actual handler call when every completed reply matches. -/
theorem observed_snapshot_of_replies {State : Type} (handler : Handler State)
    (snapshot : Bytes) (handle : Handle) (start : State) (offset : Nat)
    (counts : List Nat) (events : List Event) (finish : Phase State)
    (execution : (machine handler).Exec Mach.seqPolicy (.idle start) events finish)
    (requests : (completed events).map Exchange.request = fragmentRequests handle offset counts)
    (replies : ∀ e ∈ completed events, ReplyMatchesSnapshot snapshot e) :
    ReadsSnapshot handler snapshot handle start offset counts := by
  obtain ⟨_, valid, _⟩ := completed_exec_iff.mp execution
  exact readsSnapshot_of_trace snapshot handle offset counts valid requests replies

/-- Completed typed responses agreeing with a reference snapshot justify the
aggregate read result. The observation keeps the exact returned state and a
possible unanswered receive. -/
theorem observed_fragment_contract {State : Type} (handler : Handler State)
    (snapshot : Bytes) (handle : Handle) (start : State) (offset count : Nat)
    (rest : List Nat) (events : List Event) (finish : Phase State)
    (execution : (machine handler).Exec Mach.seqPolicy (.idle start) events finish)
    (requests : (completed events).map Exchange.request = fragmentRequests handle offset (count :: rest))
    (replies : ∀ e ∈ completed events, ReplyMatchesSnapshot snapshot e) :
    let result := readFragments handler handle start offset count rest
    (∃ reply, result.reply = some reply ∧ ReadResult snapshot offset (count + rest.sum) reply) ∧
      completed events = result.trace ∧
      ((events = encode result.trace ∧ finish = .idle result.file) ∨
       ∃ next, events = encode result.trace ++ [.recv next] ∧ finish = .pending result.file next) := by
  obtain ⟨returned, valid, shape⟩ := completed_exec_iff.mp execution
  have calls := readsSnapshot_of_trace snapshot handle offset (count :: rest) valid requests replies
  have aggregate := (read_fragments_snapshot_contract handler snapshot handle start offset count rest calls).1
  obtain ⟨exchanges, state⟩ :=
    read_fragments_reconstruct handler handle start offset count rest valid requests
  refine ⟨aggregate, exchanges, ?_⟩
  rw [exchanges, state] at shape
  exact shape

end Silmaril.Proofs.Containers.SqliteVfs.FragmentContract
