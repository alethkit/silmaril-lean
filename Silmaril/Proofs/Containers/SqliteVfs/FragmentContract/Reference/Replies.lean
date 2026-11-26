module

public import Silmaril.Containers.SqliteVfs.FragmentContract.Defs
public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Defs
import Silmaril.Containers.SqliteVfs.Completed.Thms

@[expose] public section

namespace Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Reference

open Silmaril.Containers.SqliteVfs
open Silmaril.Containers
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot (ReadsSnapshot)
open Silmaril.Containers.SqliteVfs.Completed (completed completed_exec_iff)
open Silmaril.Containers.SqliteVfs.FragmentContract (ReplyMatchesSnapshot)

private theorem trace_replies_of_snapshot {State : Type} {handler : Handler State}
    {start finish : State} {trace : Trace} (snapshot : Bytes) (handle : Handle)
    (offset : Nat) (counts : List Nat) (valid : Trace.Valid handler start trace finish)
    (requests : trace.map Exchange.request = fragmentRequests handle offset counts)
    (reads : ReadsSnapshot handler snapshot handle start offset counts) :
    ∀ e ∈ trace, ReplyMatchesSnapshot snapshot e := by
  induction counts generalizing start finish offset trace with
  | nil =>
    cases valid with
    | nil => simp
    | cons => simp [fragmentRequests] at requests
  | cons count rest ih =>
    cases valid with
    | nil => simp [fragmentRequests] at requests
    | @cons before middle final request reply tail call validTail =>
      obtain ⟨rfl, orderedTail⟩ := List.cons.inj requests
      rw [ReadsSnapshot, call] at reads
      intro e member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨Int.natCast_nonneg _, Int.natCast_nonneg _, ?_⟩
        simpa only [Int.toNat_natCast] using reads.1
      · exact ih (offset + count) validTail orderedTail reads.2 e member

/-- For an exact ordered read schedule observed from idle, the per-call
contracts on the actual handler states imply the reference contract for
every completed typed exchange. An unanswered receive contributes no reply. -/
theorem observed_replies_of_snapshot {State : Type} (handler : Handler State)
    (snapshot : Bytes) (handle : Handle) (start : State) (offset : Nat)
    (counts : List Nat) (events : List Event) (finish : Phase State)
    (execution : (machine handler).Exec Mach.seqPolicy (.idle start) events finish)
    (requests : (completed events).map Exchange.request = fragmentRequests handle offset counts)
    (reads : ReadsSnapshot handler snapshot handle start offset counts) :
    ∀ e ∈ completed events, ReplyMatchesSnapshot snapshot e := by
  obtain ⟨_, valid, _⟩ := completed_exec_iff.mp execution
  exact trace_replies_of_snapshot snapshot handle offset counts valid requests reads

end Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Reference
