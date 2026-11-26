module

public import Silmaril.Containers.SqliteVfs.FragmentContract.Defs
public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Defs
import Silmaril.Containers.SqliteVfs.FragmentContract.Thms
import Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Reference.Replies

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.FragmentContract.Reference

open Silmaril.Containers
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot (ReadsSnapshot)
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers.SqliteVfs.FragmentContract (ReplyMatchesSnapshot)

/-- For an exact ordered read schedule observed from idle, the per-call
contracts on the actual handler states imply the reference contract for
every completed typed exchange. An unanswered receive contributes no reply. -/
theorem observed_replies_of_snapshot {State : Type} (handler : Handler State)
    (snapshot : Bytes) (handle : Handle) (start : State) (offset : Nat)
    (counts : List Nat) (events : List Event) (finish : Phase State)
    (execution : (machine handler).Exec Mach.seqPolicy (.idle start) events finish)
    (requests : (completed events).map Exchange.request = fragmentRequests handle offset counts)
    (reads : ReadsSnapshot handler snapshot handle start offset counts) :
    ∀ e ∈ completed events, ReplyMatchesSnapshot snapshot e :=
  Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Reference.observed_replies_of_snapshot
    handler snapshot handle start offset counts events finish execution requests reads

/-- The observed completed replies match the reference snapshot exactly
when each actual call satisfies the same reference contract. A pending
receive contributes no completed exchange. -/
theorem observed_replies_iff_snapshot {State : Type} (handler : Handler State)
    (snapshot : Bytes) (handle : Handle) (start : State) (offset : Nat)
    (counts : List Nat) (events : List Event) (finish : Phase State)
    (execution : (machine handler).Exec Mach.seqPolicy (.idle start) events finish)
    (requests : (completed events).map Exchange.request = fragmentRequests handle offset counts) :
    (∀ e ∈ completed events, ReplyMatchesSnapshot snapshot e) ↔
      ReadsSnapshot handler snapshot handle start offset counts :=
  ⟨FragmentContract.observed_snapshot_of_replies handler snapshot handle start offset counts events finish execution requests,
    observed_replies_of_snapshot handler snapshot handle start offset counts events finish execution requests⟩

end Silmaril.Containers.SqliteVfs.FragmentContract.Reference
