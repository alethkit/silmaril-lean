module

public import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.Defs
import Silmaril.Machine.SqliteVfs.PageRead.ReadTrace.Thms
import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.Thms
import Silmaril.Machine.SqliteVfs.PageRead.MutationFrame.Thms
import Silmaril.Machine.SqliteVfs.Thms

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadTrace.DisjointWrite

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.WriteExtent (presentCount disjoint_write_agrees_iff)
open Silmaril.Machine.SqliteVfs.PageRead.ReadTrace (reads_around_trace)

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
      [⟨page.request, reply⟩, ⟨.write page.handle offset data, .ok ()⟩, ⟨page.request, reply⟩] after := by
  -- The mode component of the complete-frame theorem applies to the empty interval.
  let emptyPage : Page := ⟨page.handle, 1, 0⟩
  have mode : after.mode page.handle = before.mode page.handle :=
    (MutationFrame.write_preserves_page emptyPage write
      (by simp [emptyPage, Page.offset]) (.inl (by simp [emptyPage, Page.offset]))).2
  have afterLive : (after.mode page.handle).isNone = false := by
    rw [mode]
    exact live
  have agrees := (disjoint_write_agrees_iff page write apart).mpr extent
  have middle : Trace.Valid (readWrite capacity) before
      [⟨.write page.handle offset data, .ok ()⟩] after :=
    .cons write (.nil _)
  exact reads_around_trace (readWrite_lawful capacity).2.1 middle page
    admitted live afterLive agrees

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadTrace.DisjointWrite
