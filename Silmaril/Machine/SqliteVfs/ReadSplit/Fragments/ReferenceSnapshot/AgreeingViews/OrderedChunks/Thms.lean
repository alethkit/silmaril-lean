module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.OrderedChunks.Agreement

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.OrderedChunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments (readFragments)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews)

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
          (offset + (countsOf earlier).sum) (count :: rest)) :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.OrderedChunks.readsAgreeingViews_iff_of_ordered_chunk_references
    handler view target handle start offset chunks

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.OrderedChunks
