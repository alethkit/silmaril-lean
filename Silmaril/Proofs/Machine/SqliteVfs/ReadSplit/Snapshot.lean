module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Defs
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit

theorem range_split {offset left right : Nat}
    (whole : ReadRange offset (left + right : Nat))
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    ReadRange offset left ∧ ReadRange (offset + left : Nat) right := by
  simp only [ReadRange, Int.natCast_add] at whole ⊢
  omega

theorem read_result_combine {bytes : Bytes} {offset leftCount rightCount : Nat}
    {leftReply rightReply : ReadReply}
    (leftRead : ReadResult bytes offset leftCount leftReply)
    (rightRead : ReadResult bytes (offset + leftCount) rightCount rightReply) :
    ∃ reply, combine leftReply rightReply = some reply ∧
      ReadResult bytes offset (leftCount + rightCount) reply := by
  obtain ⟨left, rfl, leftLength, leftGet⟩ := leftRead
  obtain ⟨right, rfl, rightLength, rightGet⟩ := rightRead
  refine ⟨if offset + (leftCount + rightCount) ≤ bytes.length then .ok (left ++ right)
    else .shortRead (left ++ right), ?_, left ++ right, rfl, by simp [leftLength, rightLength], ?_⟩
  · by_cases rightFull : offset + (leftCount + rightCount) ≤ bytes.length
    · have leftFull : offset + leftCount ≤ bytes.length := by omega
      have rightFull' : offset + leftCount + rightCount ≤ bytes.length := by omega
      simp [combine, leftFull, rightFull, rightFull']
    · have rightFull' : ¬ offset + leftCount + rightCount ≤ bytes.length := by omega
      by_cases leftFull : offset + leftCount ≤ bytes.length <;>
        simp [combine, leftFull, rightFull, rightFull']
  · intro i iRange
    by_cases inLeft : i < leftCount
    · rw [List.getElem?_append_left (by simpa [leftLength] using inLeft)]
      exact leftGet i inLeft
    · rw [List.getElem?_append_right (by simpa [leftLength] using inLeft), leftLength]
      rw [rightGet (i - leftCount) (by omega)]
      congr 3
      omega


private theorem read_result_unique {bytes : Bytes} {offset count : Nat}
    {first second : ReadReply}
    (firstRead : ReadResult bytes offset count first)
    (secondRead : ReadResult bytes offset count second) : first = second := by
  obtain ⟨first, rfl, firstLength, firstGet⟩ := firstRead
  obtain ⟨second, rfl, secondLength, secondGet⟩ := secondRead
  have equal : first = second := by
    apply List.ext_getElem?
    intro i
    by_cases inRange : i < count
    · rw [firstGet i inRange, secondGet i inRange]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  rw [equal]

private theorem admitted_read {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadLaw step view) (state : State) (handle : Handle) {offset count : Nat}
    (admitted : ReadRange offset count) (live : ((view state).mode handle).isNone = false) :
    view (step state (.read handle offset count)).2 = view state ∧
      ReadResult (view state).bytes offset count (step state (.read handle offset count)).1 := by
  simpa only [live, Bool.false_eq_true, ite_false, admitted, ite_true, Int.toNat_natCast] using
    law.read state handle offset count

/-- Two admitted calls on one live handle reassemble the reply of one
larger call. Views agree at the endpoints even when the handler records
its calls in hidden state. Each trace retains its actual typed replies. -/
theorem reads_split {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadLaw step view) (state : State) (handle : Handle) {offset left right : Nat}
    (admitted : ReadRange offset (left + right : Nat))
    (leftPositive : 0 < left) (rightPositive : 0 < right)
    (live : ((view state).mode handle).isNone = false) :
    let firstReq := Request.read handle offset left
    let secondReq := Request.read handle (offset + left : Nat) right
    let wholeReq := Request.read handle offset (left + right : Nat)
    let first := step state firstReq
    let second := step first.2 secondReq
    let whole := step state wholeReq
    combine first.1 second.1 = some whole.1 ∧
      view second.2 = view whole.2 ∧
      Trace.Valid step state [⟨firstReq, first.1⟩, ⟨secondReq, second.1⟩] second.2 ∧
      Trace.Valid step state [⟨wholeReq, whole.1⟩] whole.2 := by
  dsimp only
  obtain ⟨firstAdmitted, secondAdmitted⟩ := range_split admitted leftPositive rightPositive
  obtain ⟨firstView, firstRead⟩ := admitted_read law state handle firstAdmitted live
  have secondLive : ((view (step state (.read handle offset left)).2).mode handle).isNone = false :=
    firstView ▸ live
  obtain ⟨secondView, secondRead⟩ :=
    admitted_read law (step state (.read handle offset left)).2 handle secondAdmitted secondLive
  rw [firstView] at secondRead
  obtain ⟨wholeView, wholeRead⟩ := admitted_read law state handle admitted live
  obtain ⟨combined, combinedEq, combinedRead⟩ := read_result_combine firstRead secondRead
  rw [read_result_unique combinedRead wholeRead] at combinedEq
  exact ⟨combinedEq, secondView.trans (firstView.trans wholeView.symm),
    .cons rfl (.cons rfl (.nil _)), .cons rfl (.nil _)⟩

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit
