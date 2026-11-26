module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Transport

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews

open Silmaril.Machine.SqliteVfs

/-- Per-call view contracts and agreement on the requested intervals imply
one reference contract for the actual handler schedule. -/
theorem readsSnapshot_of_agreeing_views {State : Type} (handler : Handler State)
    (view : State → Bytes) (reference : Bytes) (handle : Handle)
    (start : State) (offset : Nat) (counts : List Nat)
    (reads : ReadsAgreeingViews handler view reference handle start offset counts) :
    ReadsSnapshot handler reference handle start offset counts :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.readsSnapshot_of_agreeing_views handler view reference handle start offset counts reads

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews
