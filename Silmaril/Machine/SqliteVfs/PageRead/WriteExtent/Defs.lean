module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.WriteExtent

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- The length of the available prefix of the requested page interval. -/
def presentCount (file : FileState) (page : Page) : Nat :=
  min page.size (file.bytes.length - page.offset)

end Silmaril.Machine.SqliteVfs.PageRead.WriteExtent
