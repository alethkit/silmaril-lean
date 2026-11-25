module

public import Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Machine.SqliteVfs.Thms
import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Thms

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.RejectedMutation

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace

open Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation (keep)

private theorem rejected_write {capacity : Nat} {step : Handler FileState}
    (law : BoundedWriteLaw capacity step id)
    {before after : FileState} {handle : Handle} {offset : Int} {data : Bytes} {error : Error}
    (returns : step before (.write handle offset data) = (.error error, after)) :
    after = before := by
  have contract := law.write before handle offset data
  simp only [returns, id] at contract
  split at contract
  · exact contract.2
  · exact contract.2
  · split at contract
    · split at contract
      · cases contract.1
      · exact contract.2
    · exact contract.2

private theorem rejected_truncate {capacity : Nat} {step : Handler FileState}
    (law : BoundedWriteLaw capacity step id)
    {before after : FileState} {handle : Handle} {size : Int} {error : Error}
    (returns : step before (.truncate handle size) = (.error error, after)) :
    after = before := by
  have contract := law.truncate before handle size
  simp only [returns, id] at contract
  split at contract
  · exact contract.2
  · exact contract.2
  · split at contract
    · split at contract
      · cases contract.1
      · exact contract.2
    · exact contract.2

private theorem dropped_preserves {capacity : Nat} {step : Handler FileState}
    (law : BoundedWriteLaw capacity step id) {before after : FileState}
    {request : Request} {reply : Response request}
    (returns : step before request = (reply, after)) (dropped : keep ⟨request, reply⟩ = false) :
    after = before := by
  cases request with
  | write handle offset data =>
    cases reply with
    | ok value => cases dropped
    | error error => exact rejected_write law returns
  | truncate handle size =>
    cases reply with
    | ok value => cases dropped
    | error error => exact rejected_truncate law returns
  | _ => cases dropped

/-- Filtering a valid trace gives a valid trace of the same handler with the
same endpoints, under the bounded per-operation mutation contract. -/
theorem erase_rejected_mutations {capacity : Nat} {step : Handler FileState}
    (law : BoundedWriteLaw capacity step id) {before after : FileState} {trace : Trace}
    (valid : Trace.Valid step before trace after) :
    Trace.Valid step before (trace.filter keep) after := by
  induction valid with
  | nil => exact .nil _
  | @cons before middle after request reply rest next _ ih =>
    cases status : keep ⟨request, reply⟩ with
    | true => simpa only [List.filter_cons, status, ite_true, Bool.true_eq] using Trace.Valid.cons next ih
    | false =>
      have state := dropped_preserves law next status
      subst middle
      simpa only [List.filter_cons, status, Bool.false_eq_true, ite_false] using ih

/-- A complete page is preserved if every remaining exchange meets the
landed retaining-mutation guard. Rejected mutations are allowed in the input. -/
theorem retains_with_rejections {capacity : Nat} {before after : FileState} {trace : Trace}
    (page : Page) (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace.filter keep, RetainsPage page exchange)
    (complete : page.offset + page.size ≤ before.bytes.length) (positive : 0 < page.size) :
    CacheHit.AgreesOnPage before after page ∧ after.mode page.handle = before.mode page.handle :=
  trace_retains_page page (erase_rejected_mutations (readWrite_lawful capacity).2.2 valid)
    allowed complete positive

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.RejectedMutation
