module

public import Silmaril.Machine.SqliteVfs.ReadInterval.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ContainedReplies.Agreement

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ContainedReplies

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadInterval (presentCount)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews)

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
    ReadsAgreeingViews handler view reference handle start (outerOffset + skip) counts :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ContainedReplies.agreeingViews_of_contained_replies
    handler view reference handle outerOffset outerSize start skip counts perCall

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ContainedReplies
