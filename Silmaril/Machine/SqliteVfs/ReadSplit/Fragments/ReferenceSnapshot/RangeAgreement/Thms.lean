module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.RangeAgreement.Transport

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.RangeAgreement

open Silmaril.Machine.SqliteVfs

/-- A positive fragment schedule has the same reference contract for two
snapshots agreeing on the requested optional bytes, regardless of their
contents outside that interval. -/
theorem readsSnapshot_iff_of_range_agreement {State : Type} (handler : Handler State)
    (before after : Bytes) (handle : Handle) (start : State) (offset : Nat)
    (counts : List Nat) (positive : ∀ n ∈ counts, 0 < n)
    (agree : ∀ i, i < counts.sum → before[offset + i]? = after[offset + i]?) :
    ReadsSnapshot handler before handle start offset counts ↔
      ReadsSnapshot handler after handle start offset counts :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.RangeAgreement.readsSnapshot_iff_of_range_agreement
    handler before after handle start offset counts positive agree

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.RangeAgreement
