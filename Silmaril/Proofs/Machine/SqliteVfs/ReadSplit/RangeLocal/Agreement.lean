module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Defs
import Silmaril.Machine.SqliteVfs.ReadSplit.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.RangeLocal

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit (combine read_result_combine)

private theorem read_result_transport {before after : Bytes} {offset count : Nat}
    {reply : ReadReply} (positive : 0 < count)
    (agree : ∀ i, i < count → before[offset + i]? = after[offset + i]?)
    (result : ReadResult after offset count reply) :
    ReadResult before offset count reply := by
  have lastInside : count - 1 < count := by omega
  have lastMissing : before.length ≤ offset + (count - 1) ↔
      after.length ≤ offset + (count - 1) := by
    calc
      _ ↔ before[offset + (count - 1)]? = none := List.getElem?_eq_none_iff.symm
      _ ↔ after[offset + (count - 1)]? = none := by rw [agree _ lastInside]
      _ ↔ _ := List.getElem?_eq_none_iff
  have full : offset + count ≤ before.length ↔ offset + count ≤ after.length := by omega
  obtain ⟨buffer, status, length, bytes⟩ := result
  exact ⟨buffer, by simpa only [full] using status, length, fun i inside => by
    rw [agree i inside]
    exact bytes i inside⟩

private theorem read_result_eq_backing {bytes : Bytes} {offset count : Nat}
    {reply : ReadReply} (result : ReadResult bytes offset count reply) :
    reply = readBacking bytes offset count := by
  obtain ⟨buffer, rfl, length, contents⟩ := result
  have data : buffer = readBytes bytes offset count := by
    apply List.ext_getElem?
    intro i
    by_cases inside : i < count
    · rw [contents i inside]
      simp [readBytes, inside]
    · rw [List.getElem?_eq_none_iff.mpr (by omega : buffer.length ≤ i)]
      simp [readBytes, inside]
  simp [readBacking, data]

/-- Per-call byte contracts and stability of the second range's optional
bytes suffice to compare replies. Each schedule retains its actual endpoint. -/
theorem reads_split_of_suffix_agreement {State : Type} (step : Handler State)
    (view : State → FileState) (state : State) (handle : Handle)
    (offset left right : Nat) (rightPositive : 0 < right) :
    let firstReq := Request.read handle offset left
    let secondReq := Request.read handle (offset + left : Nat) right
    let wholeReq := Request.read handle offset (left + right : Nat)
    let first := step state firstReq
    let second := step first.2 secondReq
    let whole := step state wholeReq
    (∀ i, i < right →
      (view state).bytes[offset + left + i]? = (view first.2).bytes[offset + left + i]?) →
    ReadResult (view state).bytes offset left first.1 →
    ReadResult (view first.2).bytes (offset + left) right second.1 →
    ReadResult (view state).bytes offset (left + right) whole.1 →
    combine first.1 second.1 = some whole.1 ∧
      Trace.Valid step state [⟨firstReq, first.1⟩, ⟨secondReq, second.1⟩] second.2 ∧
      Trace.Valid step state [⟨wholeReq, whole.1⟩] whole.2 := by
  dsimp only
  intro agree firstRead secondRead wholeRead
  have secondOnInitial := read_result_transport rightPositive agree secondRead
  obtain ⟨reply, combined, combinedRead⟩ := read_result_combine firstRead secondOnInitial
  have same := (read_result_eq_backing combinedRead).trans (read_result_eq_backing wholeRead).symm
  exact ⟨combined.trans (congrArg some same), .cons rfl (.cons rfl (.nil _)), .cons rfl (.nil _)⟩

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.RangeLocal
