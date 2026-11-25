module

public import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.History.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.WriteExtent.History.Frame

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.History

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)
open Silmaril.Machine.SqliteVfs.PageRead.WriteExtent (presentCount)

/-- Optional-byte agreement through a valid disjoint write history is exactly
equality of the available page prefix counts. The handle mode is preserved. -/
theorem disjoint_write_history_agrees_iff {capacity : Nat}
    {before after : FileState} {trace : Trace} (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (covered : ∀ exchange ∈ trace, DisjointWrite page exchange) :
    (AgreesOnPage before after page ↔ presentCount before page = presentCount after page) ∧
      after.mode page.handle = before.mode page.handle :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.WriteExtent.History.disjoint_write_history_agrees_iff
    page valid covered

/-- On the admitted, live page read, reply equality is exactly equality
of the available prefix counts. Any increase makes the full page present. -/
theorem disjoint_write_history_reply_iff {capacity : Nat}
    {before after : FileState} {trace : Trace} (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (covered : ∀ exchange ∈ trace, DisjointWrite page exchange)
    (admitted : page.Admitted) (live : (before.mode page.handle).isNone = false) :
    (readWrite capacity before page.request).1 = (readWrite capacity after page.request).1 ↔
      presentCount before page = presentCount after page :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.WriteExtent.History.disjoint_write_history_reply_iff
    page valid covered admitted live

/-- When the available prefix count is equal, the same typed read exchange
can surround the valid history. -/
theorem reads_around_disjoint_write_history {capacity : Nat}
    {before after : FileState} {trace : Trace} (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (covered : ∀ exchange ∈ trace, DisjointWrite page exchange)
    (extent : presentCount before page = presentCount after page)
    (admitted : page.Admitted) (live : (before.mode page.handle).isNone = false) :
    let read : Exchange := ⟨page.request, (readWrite capacity before page.request).1⟩
    Trace.Valid (readWrite capacity) before ([read] ++ trace ++ [read]) after :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.WriteExtent.History.reads_around_disjoint_write_history
    page valid covered extent admitted live

end Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.History
