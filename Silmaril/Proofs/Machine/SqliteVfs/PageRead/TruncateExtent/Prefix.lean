module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Machine.SqliteVfs.PageRead.MutationFrame.Thms
import Silmaril.Machine.SqliteVfs.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.TruncateExtent

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)

private theorem truncate_length {capacity : Nat} {before after : FileState}
    {handle : Handle} {size : Int}
    (success : readWrite capacity before (.truncate handle size) = (.ok (), after)) :
    after.bytes.length = size.toNat := by
  have spec := (readWrite_lawful capacity).2.2.truncate before handle size
  change backing .readWrite capacity before (.truncate handle size) = (.ok (), after) at success
  simp only [Response, id, success] at spec
  split at spec
  · cases spec.1
  · cases spec.1
  · split at spec
    · split at spec
      · rw [spec.2]
        exact resize_length _ _
      · cases spec.1
    · cases spec.1

private theorem lt_prefix (page : Page) (length i : Nat) :
    i < min page.size (length - page.offset) ↔
      i < page.size ∧ page.offset + i < length := by
  rw [Nat.lt_min]
  omega

/-- A successful truncate preserves optional values at every byte in the page
exactly when it preserves the available length within the requested interval. -/
theorem truncate_agrees_iff {capacity : Nat} {before after : FileState} (page : Page)
    {size : Int}
    (success : readWrite capacity before (.truncate page.handle size) = (.ok (), after)) :
    AgreesOnPage before after page ↔
      min page.size (before.bytes.length - page.offset) =
        min page.size (size.toNat - page.offset) := by
  have length := truncate_length success
  rw [← length]
  constructor
  · intro agrees
    have same (i : Nat) : i < min page.size (before.bytes.length - page.offset) ↔
        i < min page.size (after.bytes.length - page.offset) := by
      rw [lt_prefix, lt_prefix]
      by_cases inside : i < page.size
      · simp only [inside, true_and]
        have missing :
            before.bytes.length ≤ page.offset + i ↔ after.bytes.length ≤ page.offset + i := by
          rw [← List.getElem?_eq_none_iff, ← List.getElem?_eq_none_iff, agrees i inside]
        omega
      · simp [inside]
    apply Nat.le_antisymm
    · have atRight := same (min page.size (after.bytes.length - page.offset))
      omega
    · have atLeft := same (min page.size (before.bytes.length - page.offset))
      omega
  · intro extent i inside
    have present : page.offset + i < before.bytes.length ↔
        page.offset + i < after.bytes.length := by
      have left := lt_prefix page before.bytes.length i
      have right := lt_prefix page after.bytes.length i
      rw [extent] at left
      simpa [inside] using left.symm.trans right
    by_cases beforePresent : page.offset + i < before.bytes.length
    · let bytePage : Page := ⟨page.handle, page.offset + i + 1, 1⟩
      have atByte : bytePage.offset = page.offset + i := by simp [bytePage, Page.offset]
      have kept := present.mp beforePresent
      have byteSize : 0 < bytePage.size := by
        change 0 < 1
        decide
      have framed := (MutationFrame.truncate_preserves_page bytePage success
        (show bytePage.offset + 1 ≤ before.bytes.length by omega)
        (show bytePage.offset + 1 ≤ size.toNat by omega)).1 0 byteSize
      simpa only [atByte, Nat.add_zero] using framed
    · have afterMissing := fun h => beforePresent (present.mpr h)
      rw [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt beforePresent),
        List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt afterMissing)]

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.TruncateExtent
