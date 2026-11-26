module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Chunks.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ChunkReferences.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.OrderedChunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments (readFragments)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Chunks (read_fragments_chunks)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ChunkReferences
  (readsAgreeingViews_iff_of_chunk_references)

private def scheduledCounts (chunks : List (Bytes × Nat × List Nat)) : List Nat :=
  chunks.flatMap (fun (_, count, rest) => count :: rest)

private theorem scheduledCounts_cons (reference : Bytes) (count : Nat) (rest : List Nat)
    (chunks : List (Bytes × Nat × List Nat)) :
    scheduledCounts ((reference, count, rest) :: chunks) = count :: (rest ++ scheduledCounts chunks) :=
  rfl

private theorem scheduledCounts_sum_cons (reference : Bytes) (count : Nat) (rest : List Nat)
    (chunks : List (Bytes × Nat × List Nat)) :
    (scheduledCounts ((reference, count, rest) :: chunks)).sum = count + rest.sum + (scheduledCounts chunks).sum := by
  simp only [scheduledCounts_cons, List.sum_cons, List.sum_append, Nat.add_assoc]

private def prefixEnd {State : Type} (handler : Handler State) (handle : Handle)
    (start : State) (offset : Nat) (counts : List Nat) : State :=
  match counts with
  | [] => start
  | count :: rest => (readFragments handler handle start offset count rest).file

private theorem prefixEnd_append {State : Type} (handler : Handler State) (handle : Handle)
    (start : State) (offset count : Nat) (rest remaining : List Nat) :
    prefixEnd handler handle start offset (count :: (rest ++ remaining)) =
      prefixEnd handler handle (readFragments handler handle start offset count rest).file
        (offset + count + rest.sum) remaining := by
  cases remaining with
  | nil => simp only [List.append_nil, prefixEnd]
  | cons next tail =>
    exact (read_fragments_chunks handler handle start offset count rest next tail).1

/-- Every chunk contains its first count and any remaining counts. Each local
reference agrees with the target on that chunk's interval. All chunk starts
are taken from the full preceding prefix of the same execution. The empty
list gives the empty schedule and vacuous local obligations. Zero counts
remain in the schedule and fail the existing positive-count requirement. -/
theorem readsAgreeingViews_iff_of_ordered_chunk_references {State : Type} (handler : Handler State)
    (view : State → Bytes) (target : Bytes) (handle : Handle) (start : State) (offset : Nat)
    (chunks : List (Bytes × Nat × List Nat)) :
    let countsOf := fun (schedule : List (Bytes × Nat × List Nat)) =>
      schedule.flatMap (fun (_, count, rest) => count :: rest)
    let endOf := fun (counts : List Nat) =>
      match counts with
      | [] => start
      | count :: rest => (readFragments handler handle start offset count rest).file
    (∀ earlier reference count rest later, chunks = earlier ++ (reference, count, rest) :: later →
      ∀ i, i < count + rest.sum →
        target[offset + (countsOf earlier).sum + i]? = reference[offset + (countsOf earlier).sum + i]?) →
    (ReadsAgreeingViews handler view target handle start offset (countsOf chunks) ↔
      ∀ earlier reference count rest later, chunks = earlier ++ (reference, count, rest) :: later →
        ReadsAgreeingViews handler view reference handle (endOf (countsOf earlier))
          (offset + (countsOf earlier).sum) (count :: rest)) := by
  change
    (∀ earlier reference count rest later, chunks = earlier ++ (reference, count, rest) :: later →
      ∀ i, i < count + rest.sum →
        target[offset + (scheduledCounts earlier).sum + i]? =
          reference[offset + (scheduledCounts earlier).sum + i]?) →
    (ReadsAgreeingViews handler view target handle start offset (scheduledCounts chunks) ↔
      ∀ earlier reference count rest later, chunks = earlier ++ (reference, count, rest) :: later →
        ReadsAgreeingViews handler view reference handle
          (prefixEnd handler handle start offset (scheduledCounts earlier))
          (offset + (scheduledCounts earlier).sum) (count :: rest))
  induction chunks generalizing start offset with
  | nil =>
    intro _
    constructor
    · intro _ earlier reference count rest later shape
      cases earlier <;> cases shape
    · intro _
      exact trivial
  | cons first remaining ih =>
    obtain ⟨reference, count, rest⟩ := first
    intro agreements
    let firstEnd := (readFragments handler handle start offset count rest).file
    let nextOffset := offset + count + rest.sum
    have firstAgreement : ∀ i, i < count + rest.sum → target[offset + i]? = reference[offset + i]? := by
      simpa only [scheduledCounts, List.flatMap_nil, List.sum_nil, Nat.add_zero] using
        agreements [] reference count rest remaining rfl
    have tailAgreement :
        ∀ earlier ref next tail later, remaining = earlier ++ (ref, next, tail) :: later →
          ∀ i, i < next + tail.sum →
            target[nextOffset + (scheduledCounts earlier).sum + i]? =
              ref[nextOffset + (scheduledCounts earlier).sum + i]? := by
      intro earlier ref next tail later shape
      have atChunk := agreements ((reference, count, rest) :: earlier) ref next tail later
        (by rw [shape]; rfl)
      simpa only [nextOffset, scheduledCounts_sum_cons, Nat.add_assoc] using atChunk
    have cut := readsAgreeingViews_iff_of_chunk_references handler view target reference target handle
      start offset count rest (scheduledCounts remaining) firstAgreement (fun _ _ => rfl)
    rw [scheduledCounts_cons]
    refine cut.trans ((and_congr Iff.rfl (ih firstEnd nextOffset tailAgreement)).trans ?_)
    constructor
    · rintro ⟨firstProof, tailProof⟩ earlier ref next tail later shape
      cases earlier with
      | nil =>
        cases shape
        simpa only [scheduledCounts, List.flatMap_nil, List.sum_nil, Nat.add_zero, prefixEnd] using firstProof
      | cons prior earlier =>
        obtain ⟨rfl, tailShape⟩ := List.cons.inj (show (reference, count, rest) :: remaining =
          prior :: (earlier ++ (ref, next, tail) :: later) from shape)
        have atChunk := tailProof earlier ref next tail later tailShape
        simpa only [scheduledCounts_cons, List.sum_cons, List.sum_append, prefixEnd_append,
          firstEnd, nextOffset, Nat.add_assoc] using atChunk
    · intro localProof
      refine ⟨?_, ?_⟩
      · simpa only [scheduledCounts, List.flatMap_nil, List.sum_nil, Nat.add_zero, prefixEnd] using
          localProof [] reference count rest remaining rfl
      · intro earlier ref next tail later shape
        have atChunk := localProof ((reference, count, rest) :: earlier) ref next tail later
          (by rw [shape]; rfl)
        simpa only [scheduledCounts_cons, List.sum_cons, List.sum_append, prefixEnd_append,
          firstEnd, nextOffset, Nat.add_assoc] using atChunk

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.OrderedChunks
