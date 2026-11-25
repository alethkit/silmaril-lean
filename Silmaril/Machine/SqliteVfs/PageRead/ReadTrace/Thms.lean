module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadTrace.Endpoint

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.ReadTrace

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)

/-- Two reads surrounding a valid history have the same reply when they are
admitted, live, and agree on the optional bytes at their endpoints. -/
theorem reads_around_trace {step : Handler FileState} (law : ReadLaw step id)
    {before after : FileState} {trace : Trace} (valid : Trace.Valid step before trace after)
    (page : Page) (admitted : page.Admitted) (beforeLive : (before.mode page.handle).isNone = false)
    (afterLive : (after.mode page.handle).isNone = false) (agrees : AgreesOnPage before after page) :
    let read : Exchange := ⟨page.request, (step before page.request).1⟩
    Trace.Valid step before ([read] ++ trace ++ [read]) after :=
  Proofs.Machine.SqliteVfs.PageRead.ReadTrace.reads_around_trace
    law valid page admitted beforeLive afterLive agrees

end Silmaril.Machine.SqliteVfs.PageRead.ReadTrace
