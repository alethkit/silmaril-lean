module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Machine.SqliteVfs.PageRead.ReadFrame.Thms

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadTrace

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)

private theorem append_read {step : Handler FileState} {before after : FileState}
    {trace : Trace} (valid : Trace.Valid step before trace after)
    (page : Page) (reply : Response page.request)
    (reads : step after page.request = (reply, after)) :
    Trace.Valid step before (trace ++ [⟨page.request, reply⟩]) after := by
  induction valid with
  | nil => exact .cons reads (.nil _)
  | cons first _ ih => exact .cons first (ih reads)

/-- Two reads surrounding a valid history have the same reply when they are
admitted, live, and agree on the optional bytes at their endpoints. -/
theorem reads_around_trace {step : Handler FileState} (law : ReadLaw step id)
    {before after : FileState} {trace : Trace} (valid : Trace.Valid step before trace after)
    (page : Page) (admitted : page.Admitted) (beforeLive : (before.mode page.handle).isNone = false)
    (afterLive : (after.mode page.handle).isNone = false) (agrees : AgreesOnPage before after page) :
    let read : Exchange := ⟨page.request, (step before page.request).1⟩
    Trace.Valid step before ([read] ++ trace ++ [read]) after := by
  have sameReply := ReadFrame.lawful_read_reply_agrees law law before after page
    admitted beforeLive afterLive agrees
  have unchanged (file : FileState) : (step file page.request).2 = file :=
    (law.read file page.handle page.offset page.size).1
  have readsBefore : step before page.request = ((step before page.request).1, before) :=
    Prod.ext rfl (unchanged before)
  have readsAfter : step after page.request = ((step before page.request).1, after) :=
    Prod.ext sameReply.symm (unchanged after)
  exact .cons readsBefore (append_read valid page _ readsAfter)

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadTrace
