module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.RangeAgreement.Transport

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.RangeAgreement

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews)

/-- The same actual calls and per-call view contracts can be checked
against either reference if their optional bytes agree on the schedule's range. -/
theorem readsAgreeingViews_iff_of_reference_range_agreement {State : Type} (handler : Handler State)
    (view : State → Bytes) (before after : Bytes) (handle : Handle)
    (start : State) (offset : Nat) (counts : List Nat)
    (agree : ∀ i, i < counts.sum → before[offset + i]? = after[offset + i]?) :
    ReadsAgreeingViews handler view before handle start offset counts ↔
      ReadsAgreeingViews handler view after handle start offset counts :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.RangeAgreement.readsAgreeingViews_iff_of_reference_range_agreement
    handler view before after handle start offset counts agree

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.RangeAgreement
