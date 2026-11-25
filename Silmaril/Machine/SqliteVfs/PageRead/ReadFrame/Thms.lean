module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadFrame.Reply

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.ReadFrame

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)

/-- Optional-byte agreement preserves both data and the EOF status. -/
theorem read_result_agrees {before after : FileState} (page : Page)
    {beforeReply afterReply : ReadReply} (positive : 0 < page.size)
    (agrees : AgreesOnPage before after page)
    (beforeRead : ReadResult before.bytes page.offset page.size beforeReply)
    (afterRead : ReadResult after.bytes page.offset page.size afterReply) :
    beforeReply = afterReply :=
  Proofs.Machine.SqliteVfs.PageRead.ReadFrame.read_result_agrees
    page positive agrees beforeRead afterRead

/-- For this admitted live request, any two read-lawful handlers with
agreeing observed page slices return the exact same dependent reply. -/
theorem lawful_read_reply_agrees {Left Right : Type}
    {left : Handler Left} {right : Handler Right} {leftView : Left → FileState} {rightView : Right → FileState}
    (leftLaw : ReadLaw left leftView) (rightLaw : ReadLaw right rightView)
    (before : Left) (after : Right) (page : Page) (admitted : page.Admitted)
    (leftLive : ((leftView before).mode page.handle).isNone = false)
    (rightLive : ((rightView after).mode page.handle).isNone = false)
    (agrees : AgreesOnPage (leftView before) (rightView after) page) :
    (left before page.request).1 = (right after page.request).1 :=
  Proofs.Machine.SqliteVfs.PageRead.ReadFrame.lawful_read_reply_agrees
    leftLaw rightLaw before after page admitted leftLive rightLive agrees

end Silmaril.Machine.SqliteVfs.PageRead.ReadFrame
