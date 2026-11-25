module

public import Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.RejectedMutation.Filter

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace

/-- Filtering a valid trace gives a valid trace of the same handler with the
same endpoints, under the bounded per-operation mutation contract. -/
theorem erase_rejected_mutations {capacity : Nat} {step : Handler FileState}
    (law : BoundedWriteLaw capacity step id) {before after : FileState} {trace : Trace}
    (valid : Trace.Valid step before trace after) :
    Trace.Valid step before (trace.filter keep) after :=
  Proofs.Machine.SqliteVfs.PageRead.RejectedMutation.erase_rejected_mutations law valid

/-- A complete page is preserved if every remaining exchange meets the
landed retaining-mutation guard. Rejected mutations are allowed in the input. -/
theorem retains_with_rejections {capacity : Nat} {before after : FileState} {trace : Trace}
    (page : Page) (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace.filter keep, RetainsPage page exchange)
    (complete : page.offset + page.size ≤ before.bytes.length) (positive : 0 < page.size) :
    CacheHit.AgreesOnPage before after page ∧ after.mode page.handle = before.mode page.handle :=
  Proofs.Machine.SqliteVfs.PageRead.RejectedMutation.retains_with_rejections
    page valid allowed complete positive

end Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation
