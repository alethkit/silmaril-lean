module

public import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadTrace.DisjointWrite.Trace

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.ReadTrace.DisjointWrite

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.WriteExtent (presentCount)

/-- A read, a successful disjoint write preserving the available page prefix
length, and a reread form a valid trace with the same exact read reply. -/
theorem disjoint_write_read_trace {capacity : Nat} {before after : FileState} (page : Page)
    {offset : Int} {data : Bytes}
    (admitted : page.Admitted) (live : (before.mode page.handle).isNone = false)
    (write : readWrite capacity before (.write page.handle offset data) = (.ok (), after))
    (apart : page.offset + page.size ≤ offset.toNat ∨ offset.toNat + data.length ≤ page.offset)
    (extent : presentCount before page = presentCount after page) :
    let reply := (readWrite capacity before page.request).1
    Trace.Valid (readWrite capacity) before
      [⟨page.request, reply⟩, ⟨.write page.handle offset data, .ok ()⟩, ⟨page.request, reply⟩] after :=
  Proofs.Machine.SqliteVfs.PageRead.ReadTrace.DisjointWrite.disjoint_write_read_trace
    page admitted live write apart extent

end Silmaril.Machine.SqliteVfs.PageRead.ReadTrace.DisjointWrite
