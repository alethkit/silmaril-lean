module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies.Thms
import Silmaril.Machine.SqliteVfs.ReadInterval.Subinterval.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ContainedReplies

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadInterval (presentCount)
open Silmaril.Machine.SqliteVfs.ReadInterval.Subinterval (presentCount_subinterval)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies
  (cons_of_matching_reply)

private theorem readFragments_file_step {State : Type} (handler : Handler State)
    (handle : Handle) (start : State) (offset count : Nat) (rest : List Nat) :
    (readFragments handler handle start offset count rest).file =
      let after := (handler start (.read handle offset count)).2
      match rest with
      | [] => after
      | next :: remaining => (readFragments handler handle after (offset + count) next remaining).file := by
  rw [readFragments]
  dsimp only
  cases handler start (.read handle offset count)
  cases rest <;> rfl

/-- Each matching reply is for the next contained call at the actual
endpoint of the preceding prefix. A short reply also checks the outer
interval's count on that call's input view. -/
theorem agreeingViews_of_contained_replies {State : Type} (handler : Handler State)
    (view : State → Bytes) (reference : Bytes) (handle : Handle)
    (outerOffset outerSize : Nat) (start : State) (skip : Nat) (counts : List Nat)
    (perCall : ∀ (priorCounts : List Nat) (count : Nat) (rest : List Nat), counts = priorCounts ++ count :: rest →
      let before := match priorCounts with
        | [] => start
        | first :: more => (readFragments handler handle start (outerOffset + skip) first more).file
      let displacement : Nat := skip + priorCounts.sum
      let offset : Nat := outerOffset + displacement
      let reply := (handler before (.read handle offset count)).1
      displacement + count ≤ outerSize ∧ ReadRange offset count ∧
        ReadResult reference offset count reply ∧ ReadResult (view before) offset count reply ∧
        (reference.length < offset + count →
          presentCount reference outerOffset outerSize = presentCount (view before) outerOffset outerSize)) :
    ReadsAgreeingViews handler view reference handle start (outerOffset + skip) counts := by
  induction counts generalizing start skip with
  | nil => trivial
  | cons count rest ih =>
    have first := perCall [] count rest rfl
    simp only [List.sum_nil, Nat.add_zero] at first
    obtain ⟨contained, admitted, referenceRead, actualRead, outerCount⟩ := first
    refine cons_of_matching_reply handler view reference handle start (outerOffset + skip)
      count rest admitted referenceRead actualRead rfl ?_ ?_
    · intro short
      rw [presentCount_subinterval reference outerOffset outerSize skip count contained,
        presentCount_subinterval (view start) outerOffset outerSize skip count contained, outerCount short]
    · have remaining := ih (handler start (.read handle (outerOffset + skip : Nat) count)).2
          (skip + count) (fun priorCounts next tail split => by
        have later := perCall (count :: priorCounts) next tail (by rw [split]; rfl)
        simp only [readFragments_file_step handler handle start (outerOffset + skip) count] at later
        cases priorCounts with
        | nil =>
          simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using later
        | cons first more =>
          dsimp only at later ⊢
          rw [List.sum_cons, List.sum_cons, ← Nat.add_assoc skip count,
            Nat.add_assoc outerOffset skip count] at later
          exact later)
      simpa only [Nat.add_assoc] using remaining

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ContainedReplies
