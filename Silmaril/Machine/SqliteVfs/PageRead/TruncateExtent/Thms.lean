module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.TruncateExtent.Prefix

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.TruncateExtent

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)

/-- A successful truncate preserves optional values at every byte in the page
exactly when it preserves the available length within the requested interval. -/
theorem truncate_agrees_iff {capacity : Nat} {before after : FileState} (page : Page)
    {size : Int}
    (success : readWrite capacity before (.truncate page.handle size) = (.ok (), after)) :
    AgreesOnPage before after page ↔
      min page.size (before.bytes.length - page.offset) =
        min page.size (size.toNat - page.offset) :=
  Proofs.Machine.SqliteVfs.PageRead.TruncateExtent.truncate_agrees_iff page success

end Silmaril.Machine.SqliteVfs.PageRead.TruncateExtent
