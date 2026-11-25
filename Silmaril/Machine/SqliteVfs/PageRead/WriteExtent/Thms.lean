module

public import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.WriteExtent.Prefix

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.WriteExtent

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)

/-- Agreeing optional bytes imply the same present prefix length. -/
theorem presentCount_eq_of_agreement {before after : FileState} (page : Page)
    (agrees : AgreesOnPage before after page) :
    presentCount before page = presentCount after page :=
  Proofs.Machine.SqliteVfs.PageRead.WriteExtent.presentCount_eq_of_agreement page agrees

/-- A successful disjoint write keeps the optional page bytes exactly when
it leaves the available prefix length within the requested interval equal. -/
theorem disjoint_write_agrees_iff {capacity : Nat} {before after : FileState} (page : Page)
    {offset : Int} {data : Bytes}
    (write : readWrite capacity before (.write page.handle offset data) = (.ok (), after))
    (apart : page.offset + page.size ≤ offset.toNat ∨ offset.toNat + data.length ≤ page.offset) :
    AgreesOnPage before after page ↔ presentCount before page = presentCount after page :=
  Proofs.Machine.SqliteVfs.PageRead.WriteExtent.disjoint_write_agrees_iff page write apart

end Silmaril.Machine.SqliteVfs.PageRead.WriteExtent
