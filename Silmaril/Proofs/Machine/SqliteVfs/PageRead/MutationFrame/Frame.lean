module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Machine.SqliteVfs.Thms
import Init.Data.List.Nat.TakeDrop
import Init.Omega

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationFrame

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit

private theorem resize_get (bytes : Bytes) (size index : Nat)
    (within : index < bytes.length) (kept : index < size) :
    (resize bytes size)[index]? = bytes[index]? := by
  unfold resize
  rw [List.getElem?_append_left (by simp only [List.length_take]; omega),
      List.getElem?_take_of_lt kept]

private theorem agrees_after_resize (before : FileState) (page : Page) (size : Nat)
    (complete : page.offset + page.size ≤ before.bytes.length)
    (kept : page.offset + page.size ≤ size) :
    AgreesOnPage before {before with bytes := resize before.bytes size} page := by
  intro i inside
  exact (resize_get before.bytes size (page.offset + i) (by omega) (by omega)).symm

private theorem overwrite_get_before (bytes data : Bytes) (start index : Nat)
    (within : index < bytes.length) (left : index < start) :
    (overwrite bytes start data)[index]? = bytes[index]? := by
  unfold overwrite
  have prefixBound : index < (bytes.take start).length := by simp only [List.length_take]; omega
  rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_left prefixBound, List.getElem?_take_of_lt left]

private theorem overwrite_get_after (bytes data : Bytes) (start index : Nat)
    (within : index < bytes.length) (right : start + data.length ≤ index) :
    (overwrite bytes start data)[index]? = bytes[index]? := by
  have startBound : start ≤ bytes.length := by omega
  have prefixLength :
      (bytes.take start ++ List.replicate (start - bytes.length) 0 ++ data).length =
        start + data.length := by
    simp [Nat.min_eq_left startBound, Nat.sub_eq_zero_of_le startBound]
  unfold overwrite
  rw [List.getElem?_append_right (prefixLength.symm ▸ right), prefixLength, List.getElem?_drop]
  rw [Nat.add_sub_of_le right]

private theorem agrees_after_disjoint_write (before : FileState) (page : Page)
    (start : Nat) (data : Bytes) (complete : page.offset + page.size ≤ before.bytes.length)
    (apart : page.offset + page.size ≤ start ∨ start + data.length ≤ page.offset) :
    AgreesOnPage before {before with bytes := overwrite before.bytes start data} page := by
  intro i inside
  have within : page.offset + i < before.bytes.length := by omega
  rcases apart with left | right
  · exact (overwrite_get_before before.bytes data start (page.offset + i) within (by omega)).symm
  · exact (overwrite_get_after before.bytes data start (page.offset + i) within (by omega)).symm

theorem write_preserves_page {capacity : Nat} {before after : FileState} (page : Page)
    {offset : Int} {data : Bytes}
    (write : readWrite capacity before (.write page.handle offset data) = (.ok (), after))
    (complete : page.offset + page.size ≤ before.bytes.length)
    (apart : page.offset + page.size ≤ offset.toNat ∨ offset.toNat + data.length ≤ page.offset) :
    AgreesOnPage before after page ∧ after.mode page.handle = before.mode page.handle := by
  have spec := (readWrite_lawful capacity).2.2.write before page.handle offset data
  change backing .readWrite capacity before (.write page.handle offset data) = (.ok (), after) at write
  simp only [Response, id, write] at spec
  split at spec
  · cases spec.1
  · cases spec.1
  · split at spec
    · split at spec
      · rw [spec.2]
        exact ⟨agrees_after_disjoint_write before page offset.toNat data complete apart, rfl⟩
      · cases spec.1
    · cases spec.1

theorem truncate_preserves_page {capacity : Nat} {before after : FileState} (page : Page)
    {size : Int}
    (truncate : readWrite capacity before (.truncate page.handle size) = (.ok (), after))
    (complete : page.offset + page.size ≤ before.bytes.length)
    (kept : page.offset + page.size ≤ size.toNat) :
    AgreesOnPage before after page ∧ after.mode page.handle = before.mode page.handle := by
  have spec := (readWrite_lawful capacity).2.2.truncate before page.handle size
  change backing .readWrite capacity before (.truncate page.handle size) = (.ok (), after) at truncate
  simp only [Response, id, truncate] at spec
  split at spec
  · cases spec.1
  · cases spec.1
  · split at spec
    · split at spec
      · rw [spec.2]
        exact ⟨agrees_after_resize before page size.toNat complete kept, rfl⟩
      · cases spec.1
    · cases spec.1

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationFrame
