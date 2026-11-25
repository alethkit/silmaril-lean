module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationFrame.Frame

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.MutationFrame

open CacheHit (AgreesOnPage)

/-- A successful bounded write on the page's handle preserves every byte of
a complete page when the write interval is disjoint. -/
theorem write_preserves_page {capacity : Nat} {before after : FileState} (page : Page)
    {offset : Int} {data : Bytes}
    (write : readWrite capacity before (.write page.handle offset data) = (.ok (), after))
    (complete : page.offset + page.size ≤ before.bytes.length)
    (disjoint : page.offset + page.size ≤ offset.toNat ∨ offset.toNat + data.length ≤ page.offset) :
    AgreesOnPage before after page ∧ after.mode page.handle = before.mode page.handle :=
  Proofs.Machine.SqliteVfs.PageRead.MutationFrame.write_preserves_page page write complete disjoint

/-- A successful bounded truncate on the page's handle preserves every byte
of a complete page when the new length contains the entire page. -/
theorem truncate_preserves_page {capacity : Nat} {before after : FileState} (page : Page)
    {size : Int}
    (truncate : readWrite capacity before (.truncate page.handle size) = (.ok (), after))
    (complete : page.offset + page.size ≤ before.bytes.length)
    (retained : page.offset + page.size ≤ size.toNat) :
    AgreesOnPage before after page ∧ after.mode page.handle = before.mode page.handle :=
  Proofs.Machine.SqliteVfs.PageRead.MutationFrame.truncate_preserves_page page truncate complete retained

end Silmaril.Machine.SqliteVfs.PageRead.MutationFrame
