module

public import Silmaril.Containers.SqliteVfs.FragmentContract.Defs
public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Defs
import Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Observation

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.FragmentContract

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot (ReadsSnapshot)

/-- A valid observation of the exact ordered requests determines the
contract on each actual handler call when every completed reply matches. -/
theorem observed_snapshot_of_replies {State : Type} (handler : Handler State)
    (snapshot : Bytes) (handle : Handle) (start : State) (offset : Nat)
    (counts : List Nat) (events : List Event) (finish : Phase State)
    (execution : (machine handler).Exec Mach.seqPolicy (.idle start) events finish)
    (requests : (completed events).map Exchange.request = fragmentRequests handle offset counts)
    (replies : ∀ e ∈ completed events, ReplyMatchesSnapshot snapshot e) :
    ReadsSnapshot handler snapshot handle start offset counts :=
  Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.observed_snapshot_of_replies
    handler snapshot handle start offset counts events finish execution requests replies

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
       ∃ next, events = encode result.trace ++ [.recv next] ∧ finish = .pending result.file next) :=
  Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.observed_fragment_contract
    handler snapshot handle start offset count rest events finish execution requests replies

end Silmaril.Containers.SqliteVfs.FragmentContract
