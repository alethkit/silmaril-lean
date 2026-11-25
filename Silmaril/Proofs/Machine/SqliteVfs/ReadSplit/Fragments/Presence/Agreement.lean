module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.ReadPresence.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Presence

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)
open Silmaril.Machine.SqliteVfs.PageRead.WriteExtent (presentCount)

private theorem whole_result {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadLaw step view) (state : State) (page : Page) (admitted : page.Admitted)
    (live : ((view state).mode page.handle).isNone = false) :
    ReadResult (view state).bytes page.offset page.size (step state page.request).1 := by
  simpa only [Page.request, live, Bool.false_eq_true, ite_false, admitted.2, ite_true,
    Int.toNat_natCast] using (law.read state page.handle page.offset page.size).2

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
        presentCount (leftView before) page = presentCount (rightView after) page := by
  have leftRange : ReadRange page.offset (leftCount + leftRest.sum : Nat) := leftTotal ▸ admitted.2
  have rightRange : ReadRange page.offset (rightCount + rightRest.sum : Nat) :=
    rightTotal ▸ admitted.2
  have positive : 0 < page.size :=
    leftTotal ▸ Nat.add_pos_left leftPositive leftRest.sum
  obtain ⟨beforeReply, _, _, _, _⟩ := read_fragments_sound leftLaw before page.handle page.offset
    leftCount leftRest leftPositive leftRestPositive leftRange leftLive
  obtain ⟨afterReply, _, _, _, _⟩ := read_fragments_sound rightLaw after page.handle page.offset
    rightCount rightRest rightPositive rightRestPositive rightRange rightLive
  rw [leftTotal] at beforeReply
  rw [rightTotal] at afterReply
  dsimp only
  simp only [beforeReply, afterReply]
  have agreement := Silmaril.Machine.SqliteVfs.PageRead.ReadPresence.read_result_agreement_iff page positive
    (whole_result leftLaw before page admitted leftLive)
    (whole_result rightLaw after page admitted rightLive)
  constructor
  · intro agrees
    obtain ⟨reply, count⟩ := agreement.mp agrees
    exact ⟨congrArg some reply, count⟩
  · rintro ⟨reply, count⟩
    exact agreement.mpr ⟨Option.some.inj reply, count⟩

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Presence
