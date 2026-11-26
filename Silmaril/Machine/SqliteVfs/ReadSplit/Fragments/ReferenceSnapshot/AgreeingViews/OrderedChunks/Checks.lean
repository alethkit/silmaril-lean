module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.OrderedChunks.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Thms
import Init.Omega

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.OrderedChunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews readsSnapshot_of_agreeing_views)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies (cons_of_matching_reply)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot (read_fragments_snapshot_contract)

private def file (bytes : Bytes) : FileState := ⟨bytes, some .readOnly, 0⟩
private def handle : Handle := ⟨0⟩
private def initial : FileState := file [99, 7]
private def afterFirst : FileState := file [99, 90, 13, 71]
private def afterSecond : FileState := file [99, 90, 91, 17]
private def reference : Bytes := [11, 7, 13, 17]
private def firstReference : Bytes := [55, 7, 211, 201, 202]
private def secondReference : Bytes := [88, 70, 13, 201]
private def thirdReference : Bytes := [44, 80, 130, 17]
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

private def chunks : List (Bytes × Nat × List Nat) :=
  [(firstReference, 1, []), (secondReference, 1, []), (thirdReference, 3, [])]

private def chunkCounts (parts : List (Bytes × Nat × List Nat)) : List Nat :=
  parts.flatMap (fun (_, count, rest) => count :: rest)

private def chunkStart (counts : List Nat) : FileState × Nat :=
  match counts with
  | [] => (initial, 4)
  | count :: rest => (readFragments updating handle (initial, 4) 1 count rest).file

private theorem first_local :
    ReadsAgreeingViews updating view firstReference handle (initial, 4) 1 [1] :=
  cons_of_matching_reply updating view firstReference handle (initial, 4) 1 1 []
    (by decide) (readBacking_result firstReference 1 1) (readBacking_result initial.bytes 1 1)
    rfl (fun _ => rfl) trivial

private theorem second_local :
    ReadsAgreeingViews updating view secondReference handle (afterFirst, 5) 2 [1] :=
  cons_of_matching_reply updating view secondReference handle (afterFirst, 5) 2 1 []
    (by decide) (readBacking_result secondReference 2 1) (readBacking_result afterFirst.bytes 2 1)
    rfl (fun _ => rfl) trivial

private theorem third_local :
    ReadsAgreeingViews updating view thirdReference handle (afterSecond, 6) 3 [3] :=
  cons_of_matching_reply updating view thirdReference handle (afterSecond, 6) 3 3 []
    (by decide) (readBacking_result thirdReference 3 3) (readBacking_result afterSecond.bytes 3 3)
    rfl (fun _ => rfl) trivial

private theorem chunk_facts (earlier : List (Bytes × Nat × List Nat)) (ref : Bytes)
    (count : Nat) (rest : List Nat) (later : List (Bytes × Nat × List Nat))
    (shape : chunks = earlier ++ (ref, count, rest) :: later) :
    (∀ i, i < count + rest.sum →
      reference[1 + (chunkCounts earlier).sum + i]? = ref[1 + (chunkCounts earlier).sum + i]?) ∧
      ReadsAgreeingViews updating view ref handle (chunkStart (chunkCounts earlier))
        (1 + (chunkCounts earlier).sum) (count :: rest) := by
  cases earlier with
  | nil =>
    cases shape
    refine ⟨?_, first_local⟩
    intro i inside
    change i < 1 at inside
    have : i = 0 := by omega
    subst i
    decide
  | cons first earlier =>
    obtain ⟨rfl, restShape⟩ := List.cons.inj (show
      (firstReference, 1, []) :: [(secondReference, 1, []), (thirdReference, 3, [])] =
        first :: (earlier ++ (ref, count, rest) :: later) from shape)
    cases earlier with
    | nil =>
      cases restShape
      refine ⟨?_, second_local⟩
      intro i inside
      change i < 1 at inside
      have : i = 0 := by omega
      subst i
      decide
    | cons second earlier =>
      obtain ⟨rfl, lastShape⟩ := List.cons.inj (show
        (secondReference, 1, []) :: [(thirdReference, 3, [])] =
          second :: (earlier ++ (ref, count, rest) :: later) from restShape)
      cases earlier with
      | nil =>
        cases lastShape
        refine ⟨?_, third_local⟩
        intro i inside
        change i < 3 at inside
        have indices : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases indices with rfl | rfl | rfl <;> decide
      | cons third earlier =>
        have impossible := (List.cons.inj (show [(thirdReference, 3, [])] =
          third :: (earlier ++ (ref, count, rest) :: later) from lastShape)).2
        cases earlier <;> cases impossible

example :
    chunkStart [1] = (afterFirst, 5) ∧ chunkStart [1, 1] = (afterSecond, 6) ∧
      ReadsAgreeingViews updating view firstReference handle (initial, 4) 1 [1] ∧
      ReadsAgreeingViews updating view secondReference handle (afterFirst, 5) 2 [1] ∧
      ReadsAgreeingViews updating view thirdReference handle (afterSecond, 6) 3 [3] := by
  have ordered := readsAgreeingViews_iff_of_ordered_chunk_references updating view reference handle
    (initial, 4) 1 chunks (fun earlier ref count rest later shape =>
      (chunk_facts earlier ref count rest later shape).1)
  have localProof := ordered.mp (first_agrees [1, 3] (second_agrees [3] suffix_agrees))
  exact ⟨rfl, rfl,
    localProof [] firstReference 1 [] [(secondReference, 1, []), (thirdReference, 3, [])] rfl,
    localProof [(firstReference, 1, [])] secondReference 1 [] [(thirdReference, 3, [])] rfl,
    localProof [(firstReference, 1, []), (secondReference, 1, [])] thirdReference 3 [] [] rfl⟩

example :
    let result := readFragments updating handle (initial, 4) 1 1 [1, 3]
    result.reply = some (.shortRead [7, 13, 17, 0, 0]) ∧
      ReadResult reference 1 5 (.shortRead [7, 13, 17, 0, 0]) ∧ result.file = (afterSecond, 7) := by
  have ordered := readsAgreeingViews_iff_of_ordered_chunk_references updating view reference handle
    (initial, 4) 1 chunks (fun earlier ref count rest later shape =>
      (chunk_facts earlier ref count rest later shape).1)
  have reads := ordered.mpr (fun earlier ref count rest later shape =>
    (chunk_facts earlier ref count rest later shape).2)
  have snapshot := readsSnapshot_of_agreeing_views updating view reference handle (initial, 4) 1 [1, 1, 3] reads
  obtain ⟨reply, value, contract⟩ :=
    (read_fragments_snapshot_contract updating reference handle (initial, 4) 1 1 [1, 3] snapshot).1
  change some (.shortRead [7, 13, 17, 0, 0] : ReadReply) = some reply at value
  cases value
  exact ⟨rfl, contract, rfl⟩

private theorem rejects_first_byte (ref : Bytes) (state : FileState × Nat) (offset count : Nat)
    (positive : 0 < count) (different : ref[offset]? ≠ (view state)[offset]?) :
    ¬ ReadsAgreeingViews updating view ref handle state offset [count] := by
  intro reads
  exact different (reads.2.1 0 positive)

example :
    (¬ ReadsAgreeingViews updating view firstReference handle (afterFirst, 5) 2 [1]) ∧
    (¬ ReadsAgreeingViews updating view firstReference handle (afterSecond, 6) 3 [3]) ∧
    (¬ ReadsAgreeingViews updating view secondReference handle (initial, 4) 1 [1]) ∧
    (¬ ReadsAgreeingViews updating view secondReference handle (afterSecond, 6) 3 [3]) ∧
    (¬ ReadsAgreeingViews updating view thirdReference handle (initial, 4) 1 [1]) ∧
    (¬ ReadsAgreeingViews updating view thirdReference handle (afterFirst, 5) 2 [1]) :=
  ⟨rejects_first_byte firstReference (afterFirst, 5) 2 1 (by decide) (by decide),
    rejects_first_byte firstReference (afterSecond, 6) 3 3 (by decide) (by decide),
    rejects_first_byte secondReference (initial, 4) 1 1 (by decide) (by decide),
    rejects_first_byte secondReference (afterSecond, 6) 3 3 (by decide) (by decide),
    rejects_first_byte thirdReference (initial, 4) 1 1 (by decide) (by decide),
    rejects_first_byte thirdReference (afterFirst, 5) 2 1 (by decide) (by decide)⟩

example : ¬ ReadsAgreeingViews updating view thirdReference handle (afterFirst, 5) 3 [3] :=
  rejects_first_byte thirdReference (afterFirst, 5) 3 3 (by decide) (by decide)

example : ReadsAgreeingViews updating view reference handle (initial, 4) 1 [] := by
  have ordered := readsAgreeingViews_iff_of_ordered_chunk_references updating view reference handle
    (initial, 4) 1 [] (fun earlier _ _ _ _ shape => by cases earlier <;> cases shape)
  exact ordered.mpr (fun earlier _ _ _ _ shape => by cases earlier <;> cases shape)

example :
    let result := readFragments updating handle (initial, 4) 1 0 []
    result.trace = [⟨.read handle 1 0, .error .invalidRange⟩] ∧ result.reply = none ∧
      ¬ ReadsAgreeingViews updating view reference handle (initial, 4) 1
        (chunkCounts [(reference, 0, [])]) := by
  have ordered := readsAgreeingViews_iff_of_ordered_chunk_references updating view reference handle
    (initial, 4) 1 [(reference, 0, [])] (by
      intro earlier ref count rest later shape i inside
      cases earlier with
      | nil =>
        cases shape
        exact (Nat.not_lt_zero i inside).elim
      | cons first earlier =>
        have impossible := (List.cons.inj (show [(reference, 0, [])] =
          first :: (earlier ++ (ref, count, rest) :: later) from shape)).2
        cases earlier <;> cases impossible)
  refine ⟨rfl, rfl, ?_⟩
  intro reads
  have rejected := ordered.mp reads [] reference 0 [] [] rfl
  exact Nat.lt_irrefl 0 rejected.1

private theorem two_chunk_places (left right : Bytes × Nat × List Nat)
    (earlier : List (Bytes × Nat × List Nat)) (part : Bytes × Nat × List Nat)
    (later : List (Bytes × Nat × List Nat))
    (shape : [left, right] = earlier ++ part :: later) :
    (earlier = [] ∧ part = left) ∨ (earlier = [left] ∧ part = right) := by
  cases earlier with
  | nil =>
    cases shape
    exact .inl ⟨rfl, rfl⟩
  | cons first earlier =>
    obtain ⟨rfl, pairTail⟩ := List.cons.inj (show [left, right] =
      first :: (earlier ++ part :: later) from shape)
    cases earlier with
    | nil =>
      cases pairTail
      exact .inr ⟨rfl, rfl⟩
    | cons second earlier =>
      have impossible := (List.cons.inj (show [right] =
        second :: (earlier ++ part :: later) from pairTail)).2
      cases earlier <;> cases impossible

-- This is exactly the two-chunk statement with a nonempty second chunk.
example {State : Type} (handler : Handler State) (view : State → Bytes)
    (target left right : Bytes) (handle : Handle) (start : State) (offset firstCount secondCount : Nat)
    (firstRest secondRest : List Nat)
    (firstAgreement : ∀ i, i < firstCount + firstRest.sum →
      target[offset + i]? = left[offset + i]?)
    (secondAgreement : ∀ i, i < secondCount + secondRest.sum →
      target[offset + firstCount + firstRest.sum + i]? = right[offset + firstCount + firstRest.sum + i]?) :
    ReadsAgreeingViews handler view target handle start offset
      (firstCount :: (firstRest ++ (secondCount :: secondRest))) ↔
      ReadsAgreeingViews handler view left handle start offset (firstCount :: firstRest) ∧
        ReadsAgreeingViews handler view right handle
          (readFragments handler handle start offset firstCount firstRest).file
          (offset + firstCount + firstRest.sum) (secondCount :: secondRest) := by
  let first := (left, firstCount, firstRest)
  let second := (right, secondCount, secondRest)
  have ordered := readsAgreeingViews_iff_of_ordered_chunk_references handler view target handle start offset
    [first, second] (by
      intro earlier ref count rest later shape
      rcases two_chunk_places first second earlier (ref, count, rest) later shape with
        ⟨rfl, same⟩ | ⟨rfl, same⟩
      · simp only [first, Prod.mk.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        simpa only [List.flatMap_nil, List.sum_nil, Nat.add_zero] using firstAgreement
      · simp only [second, Prod.mk.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        simpa only [first, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.sum_cons,
          Nat.add_assoc] using secondAgreement)
  constructor
  · intro whole
    have parts := ordered.mp (by
      simpa only [first, second, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.append_nil] using whole)
    refine ⟨?_, ?_⟩
    · simpa only [List.flatMap_nil, List.sum_nil, Nat.add_zero] using
        parts [] left firstCount firstRest [second] rfl
    · simpa only [first, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.sum_cons,
        Nat.add_assoc] using parts [first] right secondCount secondRest [] rfl
  · intro localProof
    have whole := ordered.mpr (by
      intro earlier ref count rest later shape
      rcases two_chunk_places first second earlier (ref, count, rest) later shape with
        ⟨rfl, same⟩ | ⟨rfl, same⟩
      · simp only [first, Prod.mk.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        simpa only [List.flatMap_nil, List.sum_nil, Nat.add_zero] using localProof.1
      · simp only [second, Prod.mk.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        simpa only [first, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.sum_cons,
          Nat.add_assoc] using localProof.2)
    simpa only [first, second, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.append_nil] using whole

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.OrderedChunks
