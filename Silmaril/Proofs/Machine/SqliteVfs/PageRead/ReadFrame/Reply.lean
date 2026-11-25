module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadFrame

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)

/-- Optional-byte agreement preserves both data and the EOF status. -/
theorem read_result_agrees {before after : FileState} (page : Page)
    {beforeReply afterReply : ReadReply} (positive : 0 < page.size)
    (agrees : AgreesOnPage before after page)
    (beforeRead : ReadResult before.bytes page.offset page.size beforeReply)
    (afterRead : ReadResult after.bytes page.offset page.size afterReply) :
    beforeReply = afterReply := by
  have lastInside : page.size - 1 < page.size := by omega
  have lastMissing :
      before.bytes.length ≤ page.offset + (page.size - 1) ↔
        after.bytes.length ≤ page.offset + (page.size - 1) := by
    calc
      _ ↔ before.bytes[page.offset + (page.size - 1)]? = none := List.getElem?_eq_none_iff.symm
      _ ↔ after.bytes[page.offset + (page.size - 1)]? = none := by rw [agrees _ lastInside]
      _ ↔ _ := List.getElem?_eq_none_iff
  have full : (page.offset + page.size ≤ before.bytes.length) ↔
      (page.offset + page.size ≤ after.bytes.length) := by omega
  obtain ⟨beforeBuffer, beforeStatus, beforeLength, beforeBytes⟩ := beforeRead
  obtain ⟨afterBuffer, afterStatus, afterLength, afterBytes⟩ := afterRead
  have buffer : beforeBuffer = afterBuffer := List.ext_getElem? fun i => by
    by_cases inside : i < page.size
    · rw [beforeBytes i inside, afterBytes i inside, agrees i inside]
    · rw [List.getElem?_eq_none_iff.mpr (by omega : beforeBuffer.length ≤ i),
        List.getElem?_eq_none_iff.mpr (by omega : afterBuffer.length ≤ i)]
  rw [beforeStatus, afterStatus, buffer]
  by_cases fits : page.offset + page.size ≤ before.bytes.length
  · rw [ite_eq_left fits, ite_eq_left (full.mp fits)]
  · have afterShort : ¬ page.offset + page.size ≤ after.bytes.length :=
      fun afterFits => fits (full.mpr afterFits)
    rw [ite_eq_right fits, ite_eq_right afterShort]

private theorem read_result_of_law {State : Type} {step : Handler State}
    {view : State → FileState} (law : ReadLaw step view) (state : State) (page : Page)
    (live : ((view state).mode page.handle).isNone = false) (admitted : page.Admitted) :
    ReadResult (view state).bytes page.offset page.size (step state page.request).1 := by
  have observed := law.read state page.handle page.offset page.size
  have range := admitted.2
  rcases run : step state page.request with ⟨reply, final⟩
  unfold Page.request at run
  simpa only [run, live, Bool.false_eq_true, ↓reduceIte, range, Int.toNat_natCast] using observed.2

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
  read_result_agrees page (Int.natCast_pos.mp admitted.2.2.1) agrees
    (read_result_of_law leftLaw before page leftLive admitted)
    (read_result_of_law rightLaw after page rightLive admitted)

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadFrame
