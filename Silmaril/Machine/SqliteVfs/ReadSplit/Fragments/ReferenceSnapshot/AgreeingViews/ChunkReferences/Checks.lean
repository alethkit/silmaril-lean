module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ChunkReferences.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Thms
import Init.Omega

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ChunkReferences

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews readsSnapshot_of_agreeing_views)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies (cons_of_matching_reply)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot (read_fragments_snapshot_contract)

private def file (bytes : Bytes) : FileState := ⟨bytes, some .readOnly, 0⟩
private def handle : Handle := ⟨0⟩
private def initial : FileState := file [99, 7]
private def afterFirst : FileState := file [99, 90, 13, 17]
private def afterSecond : FileState := file [99, 90, 91, 17]
private def reference : Bytes := [11, 7, 13, 17]
private def firstReference : Bytes := [55, 7, 13, 201, 202]
private def secondReference : Bytes := [88, 70, 130, 17]
private def realZero : Bytes := [88, 70, 130, 17, 0]
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
    ReadsAgreeingViews updating view reference handle (afterSecond, 6) 3 [3] :=
  cons_of_matching_reply updating view reference handle (afterSecond, 6) 3 3 []
    (by decide) (readBacking_result reference 3 3) (readBacking_result afterSecond.bytes 3 3)
    rfl (fun _ => rfl) trivial

private theorem first_range :
    ∀ i, i < 1 + ([1] : List Nat).sum → reference[1 + i]? = firstReference[1 + i]? := by
  intro i inside
  change i < 2 at inside
  have indices : i = 0 ∨ i = 1 := by omega
  rcases indices with rfl | rfl <;> decide

private theorem second_range :
    ∀ i, i < ([3] : List Nat).sum → reference[3 + i]? = secondReference[3 + i]? := by
  intro i inside
  change i < 3 at inside
  have indices : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases indices with rfl | rfl | rfl <;> decide

private theorem first_chunk_agrees :
    ReadsAgreeingViews updating view firstReference handle (initial, 4) 1 [1, 1] := by
  have next := cons_of_matching_reply updating view firstReference handle (afterFirst, 5) 2 1 []
    (by decide) (readBacking_result firstReference 2 1) (readBacking_result afterFirst.bytes 2 1)
    rfl (fun _ => rfl) trivial
  exact cons_of_matching_reply updating view firstReference handle (initial, 4) 1 1 [1]
    (by decide) (readBacking_result firstReference 1 1) (readBacking_result initial.bytes 1 1)
    rfl (fun _ => rfl) next

private theorem second_chunk_agrees :
    ReadsAgreeingViews updating view secondReference handle (afterSecond, 6) 3 [3] :=
  cons_of_matching_reply updating view secondReference handle (afterSecond, 6) 3 3 []
    (by decide) (readBacking_result secondReference 3 3) (readBacking_result afterSecond.bytes 3 3)
    rfl (fun _ => rfl) trivial

example :
    (readFragments updating handle (initial, 4) 1 1 [1]).file = (afterSecond, 6) ∧
      ReadsAgreeingViews updating view firstReference handle (initial, 4) 1 [1, 1] ∧
      ReadsAgreeingViews updating view secondReference handle (afterSecond, 6) 3 [3] := by
  have cut := readsAgreeingViews_iff_of_chunk_references updating view reference
    firstReference secondReference handle (initial, 4) 1 1 [1] [3] first_range second_range
  exact ⟨rfl, cut.mp (first_agrees [1, 3] (second_agrees [3] suffix_agrees))⟩

example :
    let result := readFragments updating handle (initial, 4) 1 1 [1, 3]
    result.reply = some (.shortRead [7, 13, 17, 0, 0]) ∧
      ReadResult reference 1 5 (.shortRead [7, 13, 17, 0, 0]) ∧ result.file = (afterSecond, 7) := by
  have cut := readsAgreeingViews_iff_of_chunk_references updating view reference
    firstReference secondReference handle (initial, 4) 1 1 [1] [3] first_range second_range
  have reads := cut.mpr ⟨first_chunk_agrees, second_chunk_agrees⟩
  have snapshot := readsSnapshot_of_agreeing_views updating view reference handle (initial, 4) 1 [1, 1, 3] reads
  obtain ⟨reply, value, contract⟩ :=
    (read_fragments_snapshot_contract updating reference handle (initial, 4) 1 1 [1, 3] snapshot).1
  change some (.shortRead [7, 13, 17, 0, 0] : ReadReply) = some reply at value
  cases value
  exact ⟨rfl, contract, rfl⟩

example : ¬ ReadsAgreeingViews updating view secondReference handle (initial, 4) 1 [1, 1] := by
  intro reads
  have mismatch := reads.2.1 0 (by decide)
  change some (70 : UInt8) = some 7 at mismatch
  exact (by decide : some (70 : UInt8) ≠ some 7) mismatch

example : ¬ ReadsAgreeingViews updating view firstReference handle (afterSecond, 6) 3 [3] := by
  intro reads
  have mismatch := reads.2.1 0 (by decide)
  change some (201 : UInt8) = some 17 at mismatch
  exact (by decide : some (201 : UInt8) ≠ some 17) mismatch

example :
    ReadResult secondReference 3 3 (.shortRead [17, 0, 0]) ∧
      ReadResult realZero 3 3 (.shortRead [17, 0, 0]) ∧
      ¬ (∀ i, i < ([3] : List Nat).sum → reference[3 + i]? = realZero[3 + i]?) := by
  refine ⟨readBacking_result secondReference 3 3, readBacking_result realZero 3 3, ?_⟩
  intro agreement
  have mismatch := agreement 1 (by decide)
  change none = some (0 : UInt8) at mismatch
  cases mismatch

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ChunkReferences
