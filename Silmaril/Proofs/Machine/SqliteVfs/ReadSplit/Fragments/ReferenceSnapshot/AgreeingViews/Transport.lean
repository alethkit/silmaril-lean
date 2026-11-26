module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs
import Silmaril.Machine.SqliteVfs.ReadSplit.RangeLocal.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot (ReadsSnapshot)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews)

/-- Per-call view contracts and agreement on the requested intervals imply
one reference contract for the actual handler schedule. -/
theorem readsSnapshot_of_agreeing_views {State : Type} (handler : Handler State)
    (view : State → Bytes) (reference : Bytes) (handle : Handle)
    (start : State) (offset : Nat) (counts : List Nat)
    (reads : ReadsAgreeingViews handler view reference handle start offset counts) :
    ReadsSnapshot handler reference handle start offset counts := by
  induction counts generalizing start offset with
  | nil => trivial
  | cons count rest ih =>
    simp only [ReadsAgreeingViews, ReadsSnapshot] at reads ⊢
    exact ⟨Silmaril.Machine.SqliteVfs.ReadSplit.RangeLocal.read_result_transport reads.1 reads.2.1 reads.2.2.1,
      ih _ _ reads.2.2.2⟩

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews
