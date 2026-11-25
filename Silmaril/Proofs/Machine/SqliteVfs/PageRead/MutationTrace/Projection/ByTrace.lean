module

public import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection.Defs
public import Silmaril.Machine.SqliteVfs.Thms
import Init.Data.List.Nat.TakeDrop
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Projection

private theorem resize_getD (bytes : Bytes) (size index : Nat) :
    (resize bytes size)[index]?.getD 0 = if index < size then bytes[index]?.getD 0 else 0 := by
  by_cases retained : index < size
  · rw [ite_eq_left retained]
    by_cases present : index < bytes.length
    · unfold resize
      rw [List.getElem?_append_left (by simp only [List.length_take]; omega),
        List.getElem?_take_of_lt retained]
    · unfold resize
      have takenLength : (bytes.take size).length = bytes.length := by
        simp only [List.length_take]
        omega
      rw [List.getElem?_append_right (by rw [takenLength]; omega), takenLength,
        List.getElem?_eq_none_iff.mpr (by omega : bytes.length ≤ index)]
      simp [show index - bytes.length < size - bytes.length by omega]
  · rw [ite_eq_right retained, List.getElem?_eq_none_iff.mpr (by rw [resize_length]; omega)]
    rfl

private theorem overwrite_getD (bytes data : Bytes) (start index : Nat)
    (apart : index < start ∨ start + data.length ≤ index) :
    (overwrite bytes start data)[index]?.getD 0 = bytes[index]?.getD 0 := by
  change ((resize bytes start ++ data) ++ bytes.drop (start + data.length))[index]?.getD 0 = _
  rcases apart with left | right
  · have takenLength : index < (resize bytes start).length := by rw [resize_length]; exact left
    rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_left takenLength, resize_getD, ite_eq_left left]
  · rw [List.getElem?_append_right (by simpa only [List.length_append, resize_length] using right),
      List.length_append, resize_length, List.getElem?_drop, Nat.add_sub_of_le right]

private theorem successful_write_state {capacity : Nat} {before after : FileState}
    {handle : Handle} {offset : Int} {data : Bytes}
    (step : readWrite capacity before (.write handle offset data) = (.ok (), after)) :
    after = {before with bytes := overwrite before.bytes offset.toNat data} := by
  have law := (readWrite_lawful capacity).2.2.write before handle offset data
  change backing .readWrite capacity before (.write handle offset data) = (.ok (), after) at step
  simp only [Response, id, step] at law
  split at law
  · cases law.1
  · cases law.1
  · split at law
    · split at law
      · exact law.2
      · cases law.1
    · cases law.1

private theorem successful_truncate_state {capacity : Nat} {before after : FileState}
    {handle : Handle} {size : Int}
    (step : readWrite capacity before (.truncate handle size) = (.ok (), after)) :
    after = {before with bytes := resize before.bytes size.toNat} := by
  have law := (readWrite_lawful capacity).2.2.truncate before handle size
  change backing .readWrite capacity before (.truncate handle size) = (.ok (), after) at step
  simp only [Response, id, step] at law
  split at law
  · cases law.1
  · cases law.1
  · split at law
    · split at law
      · exact law.2
      · cases law.1
    · cases law.1

private theorem mutation_getD {capacity : Nat} {before after : FileState}
    {request : Request} {response : Response request} (page : Page) (index : Nat)
    (inside : index < page.size)
    (step : readWrite capacity before request = (response, after))
    (mutation : Mutation page ⟨request, response⟩) :
    after.bytes[page.offset + index]?.getD 0 =
      if keepsIndex (page.offset + index) ⟨request, response⟩ then
        before.bytes[page.offset + index]?.getD 0 else 0 := by
  cases mutation with
  | write offset data apart =>
    rw [successful_write_state step]
    simp only [keepsIndex, ite_true]
    apply overwrite_getD
    omega
  | truncate size =>
    rw [successful_truncate_state step]
    simp only [keepsIndex, decide_eq_true_eq]
    exact resize_getD _ _ _

/-- A byte's padded value survives exactly by the per-truncate retention rule.
A value outside the original file or removed by a truncate is now padded zero.
This does not identify a zero already present with an absent byte. -/
private theorem trace_getD {capacity : Nat} {before after : FileState} {trace : Trace}
    (page : Page) (index : Nat) (inside : index < page.size)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace, Mutation page exchange) :
    after.bytes[page.offset + index]?.getD 0 =
      if trace.all (keepsIndex (page.offset + index)) then before.bytes[page.offset + index]?.getD 0 else 0 := by
  induction valid with
  | nil => rfl
  | @cons before middle after request response rest next _ ih =>
    have first := mutation_getD page index inside next (allowed ⟨request, response⟩ (by simp))
    have later := ih (fun exchange member => allowed exchange (List.mem_cons_of_mem _ member))
    rw [later, first, List.all_cons]
    cases keepsIndex (page.offset + index) ⟨request, response⟩ <;>
      cases rest.all (keepsIndex (page.offset + index)) <;> rfl

theorem trace_extent_mode {capacity : Nat} {before after : FileState} {trace : Trace}
    (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace, Mutation page exchange) :
    after.bytes.length = projectedExtent trace before.bytes.length ∧
      after.mode page.handle = before.mode page.handle := by
  induction valid with
  | nil => exact ⟨rfl, rfl⟩
  | @cons before middle after request response rest next _ ih =>
    have covered := allowed ⟨request, response⟩ (by simp)
    obtain ⟨size, mode⟩ := ih (fun exchange member => allowed exchange (List.mem_cons_of_mem _ member))
    have step : middle.bytes.length = projectedExtent.step before.bytes.length ⟨request, response⟩ ∧
        middle.mode page.handle = before.mode page.handle := by
      cases covered with
      | write offset data _ =>
        rw [successful_write_state next]
        exact ⟨overwrite_length _ _ _, rfl⟩
      | truncate amount =>
        rw [successful_truncate_state next]
        exact ⟨resize_length _ _, rfl⟩
    refine ⟨?_, mode.trans step.2⟩
    simpa only [projectedExtent, List.foldl_cons, ← step.1] using size

/-- The extent fold decides final presence. The original byte can survive
only if it was present initially and every truncate retained its index. -/
theorem trace_optional_byte {capacity : Nat} {before after : FileState} {trace : Trace}
    (page : Page) (index : Nat) (inside : index < page.size)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace, Mutation page exchange) :
    after.bytes[page.offset + index]? = projectedByte? before trace (page.offset + index) := by
  unfold projectedByte?
  rw [← (trace_extent_mode page valid allowed).1]
  by_cases present : page.offset + index < after.bytes.length
  · rw [ite_eq_left present, ← trace_getD page index inside valid allowed, List.getElem?_eq_getElem present]
    rfl
  · rw [ite_eq_right present, List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt present)]

/-- The initial bytes and the bounded mutation exchanges determine the exact
reply to a final admitted, live read of the selected page. -/
theorem trace_read_reply {capacity : Nat} {before after : FileState} {trace : Trace}
    (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace, Mutation page exchange)
    (admitted : page.Admitted) (live : (before.mode page.handle).isNone = false) :
    (readWrite capacity after page.request).1 = projectedRead before trace page := by
  obtain ⟨length, mode⟩ := trace_extent_mode page valid allowed
  have afterLive : (after.mode page.handle).isNone = false := congrArg Option.isNone mode |>.trans live
  have read : (readWrite capacity after page.request).1 = readBacking after.bytes page.offset page.size := by
    simp [Page.request, readWrite, backing, afterLive, admitted.2]
    rfl
  have buffer : readBytes after.bytes page.offset page.size = List.ofFn (fun i : Fin page.size =>
      (projectedByte? before trace (page.offset + i)).getD 0) := by
    unfold readBytes
    congr 1
    funext i
    exact congrArg (fun byte : Option UInt8 => byte.getD 0)
      (trace_optional_byte page i i.isLt valid allowed)
  rw [read]
  unfold readBacking projectedRead
  rw [length, buffer]

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace.Projection
