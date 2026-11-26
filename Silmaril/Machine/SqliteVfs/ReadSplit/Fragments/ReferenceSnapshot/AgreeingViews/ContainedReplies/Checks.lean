module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ContainedReplies.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Thms
import Init.Omega

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ContainedReplies

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadInterval (presentCount)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews

private def file (bytes : Bytes) : FileState := ⟨bytes, some .readOnly, 0⟩
private def token : Handle := ⟨0⟩
private def initial : FileState := file [99, 7]
private def changed : FileState := file [99, 90, 13]
private def reference : Bytes := [11, 7, 13]
private def view (state : FileState × Nat) : Bytes := state.1.bytes
private def updating : Handler (FileState × Nat) := fun state request =>
  let call := readOnly 8 state.1 request
  (call.1, { call.2 with bytes := changed.bytes }, state.2 + 1)

private theorem readBacking_result (data : Bytes) (offset count : Nat) :
    ReadResult data offset count (readBacking data offset count) := by
  refine ⟨readBytes data offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

-- The first full reply needs no equality of the two outer counts.
-- The short reply is checked against the view after that first call.
example :
    presentCount initial.bytes 0 4 ≠ presentCount reference 0 4 ∧
      ReadResult reference 1 3 (.shortRead [7, 13, 0]) ∧
      (readFragments updating token (initial, 4) 1 1 [2]).reply = some (.shortRead [7, 13, 0]) ∧
      (readFragments updating token (initial, 4) 1 1 [2]).file = (changed, 6) := by
  have agrees := agreeingViews_of_contained_replies updating view reference token 0 4 (initial, 4) 1
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
      | cons first priorCounts =>
        simp at split
        obtain ⟨rfl, split⟩ := split
        cases priorCounts with
        | nil =>
          simp at split
          obtain ⟨rfl, rfl⟩ := split
          exact ⟨by decide, by decide, readBacking_result reference 2 2,
            readBacking_result changed.bytes 2 2, fun _ => rfl⟩
        | cons second more =>
          simp at split)
  have snapshot := readsSnapshot_of_agreeing_views updating view reference token (initial, 4) 1 [1, 2] agrees
  obtain ⟨reply, value, result⟩ :=
    (read_fragments_snapshot_contract updating reference token (initial, 4) 1 1 [2] snapshot).1
  change some (.shortRead [7, 13, 0] : ReadReply) = some reply at value
  cases value
  exact ⟨by decide, result, rfl, rfl⟩

private def empty : FileState := file []
private def regrown : FileState := file [99, 88, 0]
private def oneZero : Bytes := [0]
private def growing : Handler FileState := fun state request =>
  let call := readOnly 8 state request
  (call.1, { call.2 with bytes := regrown.bytes })

-- Equal totals and a matching first typed short reply still leave unequal
-- outer counts on the first actual input view.
example :
    let first := growing empty (.read token 0 2)
    let second := growing first.2 (.read token 2 2)
    first.1 = readBacking oneZero 0 2 ∧ second.1 = readBacking oneZero 2 2 ∧
      ReadResult empty.bytes 0 2 first.1 ∧ ReadResult first.2.bytes 2 2 second.1 ∧
      presentCount empty.bytes 0 2 + presentCount first.2.bytes 2 2 = presentCount oneZero 0 4 ∧
      ¬ (oneZero.length < 0 + 2 →
        presentCount oneZero 0 4 = presentCount empty.bytes 0 4) := by
  refine ⟨rfl, rfl, readBacking_result empty.bytes 0 2, readBacking_result regrown.bytes 2 2,
    rfl, ?_⟩
  intro outerCount
  exact (by decide : (1 : Nat) ≠ 0) (outerCount (by decide))

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ContainedReplies
