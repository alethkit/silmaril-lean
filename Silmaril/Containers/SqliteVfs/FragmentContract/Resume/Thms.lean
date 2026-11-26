module

public import Silmaril.Containers.SqliteVfs.FragmentContract.Defs
public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Resume.Extend

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.FragmentContract.Resume

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers.SqliteVfs.FragmentContract (ReplyMatchesSnapshot)

/-- Complete the next fragment while keeping a reference-snapshot contract.
Only the new actual reply needs to be checked in addition to the prefix replies. -/
theorem complete_pending_fragment_contract {State : Type} (handler : Handler State)
    (snapshot : Bytes) (handle : Handle) (start : State) (offset count : Nat)
    (rest : List Nat) (nextCount : Nat) (events : List Event) :
    let before := readFragments handler handle start offset count rest
    let next : Request := .read handle (offset + count + rest.sum : Nat) nextCount
    let call := handler before.file next
    let response : Exchange := ⟨next, call.1⟩
    let extended := readFragments handler handle start offset count (rest ++ [nextCount])
    (machine handler).Exec Mach.seqPolicy (.idle start) events (.pending before.file next) →
    (completed events).map Exchange.request = fragmentRequests handle offset (count :: rest) →
    (∀ e ∈ completed events, ReplyMatchesSnapshot snapshot e) →
    ReplyMatchesSnapshot snapshot response →
    (∃ reply, extended.reply = some reply ∧
      ReadResult snapshot offset (count + rest.sum + nextCount) reply) ∧
      extended.file = call.2 ∧ completed (events ++ [.send response]) = extended.trace ∧
      (machine handler).Exec Mach.seqPolicy (.idle start) (events ++ [.send response]) (.idle call.2) :=
  Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Resume.complete_pending_fragment_contract
    handler snapshot handle start offset count rest nextCount events

end Silmaril.Containers.SqliteVfs.FragmentContract.Resume
