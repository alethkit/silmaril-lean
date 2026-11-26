module

public import Silmaril.Containers.SqliteVfs.FragmentContract.Defs
public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Containers.SqliteVfs.FragmentContract.Thms
import Silmaril.Containers.SqliteVfs.FragmentResume.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Thms

@[expose] public section

namespace Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Resume

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers.SqliteVfs.FragmentContract (ReplyMatchesSnapshot)
open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.FragmentContract (observed_fragment_contract)
open Silmaril.Containers.SqliteVfs.FragmentResume (complete_pending_fragment)
open Silmaril.Machine.SqliteVfs.ReadSplit (read_result_combine)

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
      (machine handler).Exec Mach.seqPolicy (.idle start) (events ++ [.send response]) (.idle call.2) := by
  dsimp only
  intro execution requests replies nextReply
  let before := readFragments handler handle start offset count rest
  let next : Request := .read handle (offset + count + rest.sum : Nat) nextCount
  let call := handler before.file next
  obtain ⟨⟨left, beforeReply, leftRead⟩, _, _⟩ := observed_fragment_contract
    handler snapshot handle start offset count rest events (.pending before.file next)
    execution requests replies
  have rightRead : ReadResult snapshot (offset + (count + rest.sum)) nextCount call.1 := by
    simpa only [Int.toNat_natCast, Nat.add_assoc] using nextReply.2.2
  obtain ⟨reply, combined, contract⟩ := read_result_combine leftRead rightRead
  obtain ⟨_, _, file, aggregate, finished, projection⟩ :=
    complete_pending_fragment handler handle start offset count rest nextCount events execution requests
  refine ⟨⟨reply, ?_, contract⟩, file, projection, finished⟩
  rw [aggregate, beforeReply]
  exact combined

end Silmaril.Proofs.Containers.SqliteVfs.FragmentContract.Resume
