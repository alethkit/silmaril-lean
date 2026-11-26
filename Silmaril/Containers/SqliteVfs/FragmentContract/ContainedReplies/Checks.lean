module

import Silmaril.Containers.SqliteVfs.FragmentContract.ContainedReplies.Thms
import Silmaril.Containers.SqliteVfs.FragmentPrefix.Thms
import Silmaril.Containers.SqliteVfs.Completed.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ContainedReplies.Thms
import Init.Omega

namespace Silmaril.Containers.SqliteVfs.FragmentContract.ContainedReplies

open Silmaril.Containers
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ContainedReplies (agreeingViews_of_contained_replies)
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers.SqliteVfs.FragmentPrefix (exec_fragment_prefix_iff)

private def file (bytes : Bytes) : FileState := ⟨bytes, some .readOnly, 0⟩
private def handle : Handle := ⟨0⟩
private def initial : FileState := file [99, 7]
private def changed : FileState := file [99, 90, 13]
private def reference : Bytes := [11, 7, 13]
private def view (state : FileState × Nat) : Bytes := state.1.bytes
private def updating : Handler (FileState × Nat) := fun state request =>
  let call := readOnly 8 state.1 request
  (call.1, { call.2 with bytes := changed.bytes }, state.2 + 1)

private def first : Exchange := ⟨.read handle 1 1, .ok [7]⟩
private def second : Exchange := ⟨.read handle 2 2, .shortRead [13, 0]⟩
private def pendingRead : Request := .read handle 4 0
private def rejected : Exchange := ⟨pendingRead, .error .invalidRange⟩

private theorem readBacking_result (data : Bytes) (offset count : Nat) :
    ReadResult data offset count (readBacking data offset count) := by
  refine ⟨readBytes data offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

private theorem prefix_agrees : ReadsAgreeingViews updating view reference handle (initial, 4) 1 [1, 2] :=
  agreeingViews_of_contained_replies updating view reference handle 0 4 (initial, 4) 1
    [1, 2] (fun priorCounts count rest split => by
      cases priorCounts with
      | nil =>
        simp at split
        obtain ⟨rfl, rfl⟩ := split
        refine ⟨by decide, by decide, readBacking_result reference 1 1,
          readBacking_result initial.bytes 1 1, ?_⟩
        intro short
        change (3 : Nat) < 2 at short
        omega
      | cons firstCount priorCounts =>
        simp at split
        obtain ⟨rfl, split⟩ := split
        cases priorCounts with
        | nil =>
          simp at split
          obtain ⟨rfl, rfl⟩ := split
          exact ⟨by decide, by decide, readBacking_result reference 2 2,
            readBacking_result changed.bytes 2 2, fun _ => rfl⟩
        | cons secondCount more =>
          simp at split)

example :
    let events := encode [first, second]
    completed events = [first, second] ∧
      ReadResult reference 1 3 (.shortRead [7, 13, 0]) ∧
      (readFragments updating handle (initial, 4) 1 1 [2]).reply = some (.shortRead [7, 13, 0]) ∧
      (machine updating).Exec Mach.seqPolicy (.idle (initial, 4)) events (.idle (changed, 6)) := by
  let events := encode [first, second]
  have run := (exec_fragment_prefix_iff updating handle (initial, 4) 1 1 [2]
    events (.idle (changed, 6))).mpr (.inl ⟨rfl, rfl⟩)
  obtain ⟨⟨reply, exactReply, contract⟩, projection, _⟩ :=
    observed_of_agreeing_views updating reference view handle (initial, 4) 1 1 [2]
      events (.idle (changed, 6)) run.1 run.2 prefix_agrees
  change some (.shortRead [7, 13, 0] : ReadReply) = some reply at exactReply
  cases exactReply
  exact ⟨projection, contract, rfl, run.1⟩

example :
    let events := encode [first, second] ++ [.recv pendingRead]
    completed events = [first, second] ∧
      (completed events).map Exchange.request ≠ fragmentRequests handle 1 [1, 2, 0] ∧
      (machine updating).Exec Mach.seqPolicy (.idle (initial, 4)) events (.pending (changed, 6) pendingRead) := by
  let events := encode [first, second] ++ [.recv pendingRead]
  have run := (exec_fragment_prefix_iff updating handle (initial, 4) 1 1 [2]
    events (.pending (changed, 6) pendingRead)).mpr (.inr ⟨pendingRead, rfl, rfl⟩)
  have checked := observed_of_agreeing_views updating reference view handle (initial, 4) 1 1 [2]
    events (.pending (changed, 6) pendingRead) run.1 run.2 prefix_agrees
  refine ⟨checked.2.1, ?_, run.1⟩
  rw [run.2]
  decide

example :
    completed [.recv pendingRead] = [] ∧
      (∀ count rest, (completed [.recv pendingRead]).map Exchange.request ≠
        fragmentRequests handle 4 (count :: rest)) ∧
      (machine updating).Exec Mach.seqPolicy (.idle (changed, 6)) [.recv pendingRead]
        (.pending (changed, 6) pendingRead) := by
  refine ⟨rfl, ?_, Completed.completed_exec_iff.mpr
    ⟨(changed, 6), .nil _, .inr ⟨pendingRead, rfl, rfl⟩⟩⟩
  intro count rest equal
  cases equal

example :
    let events := encode [first, second, rejected]
    completed events = [first, second, rejected] ∧
      (readFragments updating handle (initial, 4) 1 1 [2, 0]).reply = none ∧
      (machine updating).Exec Mach.seqPolicy (.idle (initial, 4)) events (.idle (changed, 7)) := by
  have run := (exec_fragment_prefix_iff updating handle (initial, 4) 1 1 [2, 0]
    (encode [first, second, rejected]) (.idle (changed, 7))).mpr (.inl ⟨rfl, rfl⟩)
  exact ⟨rfl, rfl, run.1⟩

end Silmaril.Containers.SqliteVfs.FragmentContract.ContainedReplies
