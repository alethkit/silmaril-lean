module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Chunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments (readFragments)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews)

/-- Split or recombine the per-call agreement at a nonempty executed
prefix. The suffix uses that prefix's returned state and end offset. -/
theorem readsAgreeingViews_append_iff {State : Type} (handler : Handler State) (view : State → Bytes)
    (reference : Bytes) (handle : Handle) (start : State) (offset count : Nat)
    (prefixRest suffix : List Nat) :
    ReadsAgreeingViews handler view reference handle start offset (count :: (prefixRest ++ suffix)) ↔
      ReadsAgreeingViews handler view reference handle start offset (count :: prefixRest) ∧
        ReadsAgreeingViews handler view reference handle
          (readFragments handler handle start offset count prefixRest).file
          (offset + count + prefixRest.sum) suffix := by
  induction prefixRest generalizing start offset count with
  | nil =>
    let call := handler start (.read handle offset count)
    let same := ∀ i : Nat, i < count → reference[offset + i]? = (view start)[offset + i]?
    change
      (0 < count ∧ same ∧ ReadResult (view start) offset count call.1 ∧
        ReadsAgreeingViews handler view reference handle call.2 (offset + count) suffix) ↔
      (0 < count ∧ same ∧ ReadResult (view start) offset count call.1 ∧ True) ∧
        ReadsAgreeingViews handler view reference handle call.2 (offset + count) suffix
    simp only [and_true, and_assoc]
  | cons next tail ih =>
    let call := handler start (.read handle offset count)
    let same := ∀ i : Nat, i < count → reference[offset + i]? = (view start)[offset + i]?
    change
      (0 < count ∧ same ∧ ReadResult (view start) offset count call.1 ∧
        ReadsAgreeingViews handler view reference handle call.2 (offset + count)
          (next :: (tail ++ suffix))) ↔
      (0 < count ∧ same ∧ ReadResult (view start) offset count call.1 ∧
        ReadsAgreeingViews handler view reference handle call.2 (offset + count) (next :: tail)) ∧
        ReadsAgreeingViews handler view reference handle
          (readFragments handler handle call.2 (offset + count) next tail).file
          (offset + count + (next :: tail).sum) suffix
    rw [ih call.2 (offset + count) next]
    simp only [List.sum_cons, Nat.add_assoc, and_assoc]

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Chunks
