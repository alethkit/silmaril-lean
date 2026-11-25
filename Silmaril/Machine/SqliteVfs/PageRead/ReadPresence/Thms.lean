module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadPresence.Recover

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.ReadPresence

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- Two valid stable-snapshot reads of a positive-size page agree on its
optional bytes exactly when both the typed replies and the available
prefix counts agree. -/
theorem read_result_agreement_iff {before after : FileState} (page : Page)
    {beforeReply afterReply : ReadReply} (positive : 0 < page.size)
    (beforeRead : ReadResult before.bytes page.offset page.size beforeReply)
    (afterRead : ReadResult after.bytes page.offset page.size afterReply) :
    CacheHit.AgreesOnPage before after page ↔
      beforeReply = afterReply ∧ WriteExtent.presentCount before page = WriteExtent.presentCount after page :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadPresence.read_result_agreement_iff page positive beforeRead afterRead

end Silmaril.Machine.SqliteVfs.PageRead.ReadPresence
