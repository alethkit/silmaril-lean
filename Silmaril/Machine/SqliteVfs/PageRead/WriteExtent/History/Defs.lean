module

public import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.History

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- One completed successful write on this page's handle with a disjoint
write interval. Trace validity supplies range, mode and capacity checks. -/
inductive DisjointWrite (page : Page) : Exchange → Prop where
  | write (offset : Int) (data : Bytes)
      (apart : page.offset + page.size ≤ offset.toNat ∨ offset.toNat + data.length ≤ page.offset) :
      DisjointWrite page ⟨.write page.handle offset data, .ok ()⟩

end Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.History
