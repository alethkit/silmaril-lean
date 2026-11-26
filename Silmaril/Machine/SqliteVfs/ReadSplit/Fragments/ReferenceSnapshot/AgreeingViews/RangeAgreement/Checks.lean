module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.RangeAgreement.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies.Thms
import Init.Omega

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.RangeAgreement

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
private def differentOutside : Bytes := [55, 7, 13, 17]
private def realZero : Bytes := [11, 7, 13, 17, 0]
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

private theorem in_range :
    ∀ i, i < ([1, 1, 3] : List Nat).sum → reference[1 + i]? = differentOutside[1 + i]? := by
  intro i inside
  change i < 5 at inside
  have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases indices with rfl | rfl | rfl | rfl | rfl <;> decide

example :
    reference[0]? ≠ differentOutside[0]? ∧
      ReadsAgreeingViews updating view differentOutside handle (initial, 4) 1 [1, 1, 3] ∧
      ReadsAgreeingViews updating view reference handle (initial, 4) 1 [1, 1, 3] ∧
      (readFragments updating handle (initial, 4) 1 1 [1, 3]).reply = some (.shortRead [7, 13, 17, 0, 0]) ∧
      (readFragments updating handle (initial, 4) 1 1 [1, 3]).file = (afterSecond, 7) := by
  have reads := first_agrees [1, 3] (second_agrees [3] suffix_agrees)
  have swap := readsAgreeingViews_iff_of_reference_range_agreement updating view reference differentOutside
    handle (initial, 4) 1 [1, 1, 3] in_range
  have other := swap.mp reads
  exact ⟨by decide, other, swap.mpr other, rfl, rfl⟩

example :
    ReadResult reference 3 3 (.shortRead [17, 0, 0]) ∧
      ReadResult realZero 3 3 (.shortRead [17, 0, 0]) ∧
      ¬ (∀ i, i < ([1, 1, 3] : List Nat).sum → reference[1 + i]? = realZero[1 + i]?) ∧
      ¬ ReadsAgreeingViews updating view realZero handle (afterSecond, 6) 3 [3] := by
  refine ⟨readBacking_result reference 3 3, readBacking_result realZero 3 3, ?_, ?_⟩
  · intro agree
    have mismatch := agree 3 (by decide)
    change none = some (0 : UInt8) at mismatch
    cases mismatch
  · intro reads
    have mismatch := reads.2.1 1 (by decide)
    change some (0 : UInt8) = none at mismatch
    cases mismatch

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.RangeAgreement
