module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Chunks.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies.Thms
import Init.Omega

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Chunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies (cons_of_matching_reply)

private def file (bytes : Bytes) : FileState := ⟨bytes, some .readOnly, 0⟩
private def handle : Handle := ⟨0⟩
private def initial : FileState := file [99, 7]
private def afterFirst : FileState := file [99, 90, 13, 17]
private def afterSecond : FileState := file [99, 90, 91, 17]
private def reference : Bytes := [11, 7, 13, 17]
private def view (state : FileState × Nat) : Bytes := state.1.bytes
private def updating : Handler (FileState × Nat) := fun state request =>
  let call := readOnly 8 state.1 request
  let bytes := if state.2 = 4 then afterFirst.bytes else afterSecond.bytes
  (call.1, { call.2 with bytes }, state.2 + 1)

private theorem readBacking_result (data : Bytes) (offset count : Nat) :
    ReadResult data offset count (readBacking data offset count) := by
  refine ⟨readBytes data offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

private theorem first_agrees (rest : List Nat)
    (remaining : ReadsAgreeingViews updating view reference handle (afterFirst, 5) 2 rest) :
    ReadsAgreeingViews updating view reference handle (initial, 4) 1 (1 :: rest) := by
  refine cons_of_matching_reply updating view reference handle (initial, 4) 1 1 rest
    (by decide) (readBacking_result reference 1 1) (readBacking_result initial.bytes 1 1)
    rfl ?_ remaining
  intro short
  change (4 : Nat) < 2 at short
  omega

private theorem second_agrees (rest : List Nat)
    (remaining : ReadsAgreeingViews updating view reference handle (afterSecond, 6) 3 rest) :
    ReadsAgreeingViews updating view reference handle (afterFirst, 5) 2 (1 :: rest) :=
  cons_of_matching_reply updating view reference handle (afterFirst, 5) 2 1 rest
    (by decide) (readBacking_result reference 2 1) (readBacking_result afterFirst.bytes 2 1)
    rfl (fun _ => rfl) remaining

private theorem suffix_agrees :
    ReadsAgreeingViews updating view reference handle (afterSecond, 6) 3 [2] :=
  cons_of_matching_reply updating view reference handle (afterSecond, 6) 3 2 []
    (by decide) (readBacking_result reference 3 2) (readBacking_result afterSecond.bytes 3 2)
    rfl (fun _ => rfl) trivial

example :
    ReadsAgreeingViews updating view reference handle (initial, 4) 1 [1, 1, 2] :=
  (readsAgreeingViews_append_iff updating view reference handle (initial, 4) 1 1 [1] [2]).mpr
    ⟨first_agrees [1] (second_agrees [] trivial), suffix_agrees⟩

example :
    (readFragments updating handle (initial, 4) 1 1 [1]).file = (afterSecond, 6) ∧
    ReadsAgreeingViews updating view reference handle (initial, 4) 1 [1, 1] ∧
    ReadsAgreeingViews updating view reference handle (afterSecond, 6) 3 [2] := by
  have full := first_agrees [1, 2] (second_agrees [2] suffix_agrees)
  exact ⟨rfl, (readsAgreeingViews_append_iff updating view reference handle (initial, 4) 1 1 [1] [2]).mp full⟩

example : ¬ ReadsAgreeingViews updating view reference handle (initial, 4) 3 [2] := by
  intro agrees
  have mismatch := agrees.2.1 0 (by decide)
  change some (17 : UInt8) = none at mismatch
  cases mismatch

example : ¬ ReadsAgreeingViews updating view reference handle (afterSecond, 6) 2 [2] := by
  intro agrees
  have mismatch := agrees.2.1 0 (by decide)
  change some (13 : UInt8) = some 91 at mismatch
  exact (by decide : some (13 : UInt8) ≠ some 91) mismatch

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Chunks
