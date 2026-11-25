module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.ReadPresence.Thms
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Presence.Agreement

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Presence

open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)
open Silmaril.Machine.SqliteVfs.PageRead.WriteExtent (presentCount)

/-- Two separately fragmented reads determine agreement on the presence and
value of every requested byte from their exact replies and present counts.
Each partition can use its own boundaries and read-lawful handler. -/
theorem fragment_reply_agreement_iff {Left Right : Type}
    {left : Handler Left} {right : Handler Right}
    {leftView : Left → FileState} {rightView : Right → FileState}
    (leftLaw : ReadLaw left leftView) (rightLaw : ReadLaw right rightView)
    (before : Left) (after : Right) (page : Page) (admitted : page.Admitted)
    (leftLive : ((leftView before).mode page.handle).isNone = false)
    (rightLive : ((rightView after).mode page.handle).isNone = false)
    (leftCount rightCount : Nat) (leftRest rightRest : List Nat)
    (leftPositive : 0 < leftCount) (rightPositive : 0 < rightCount)
    (leftRestPositive : ∀ n ∈ leftRest, 0 < n)
    (rightRestPositive : ∀ n ∈ rightRest, 0 < n)
    (leftTotal : leftCount + leftRest.sum = page.size)
    (rightTotal : rightCount + rightRest.sum = page.size) :
    let beforeRead := readFragments left page.handle before page.offset leftCount leftRest
    let afterRead := readFragments right page.handle after page.offset rightCount rightRest
    AgreesOnPage (leftView before) (rightView after) page ↔
      beforeRead.reply = afterRead.reply ∧
        presentCount (leftView before) page = presentCount (rightView after) page :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Presence.fragment_reply_agreement_iff
    leftLaw rightLaw before after page admitted leftLive rightLive
    leftCount rightCount leftRest rightRest leftPositive rightPositive
    leftRestPositive rightRestPositive leftTotal rightTotal

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Presence
