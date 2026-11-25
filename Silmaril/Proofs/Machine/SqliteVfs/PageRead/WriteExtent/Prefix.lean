module

public import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Machine.SqliteVfs.PageRead.MutationFrame.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.WriteExtent

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)
open Silmaril.Machine.SqliteVfs.PageRead.WriteExtent (presentCount)

private theorem presentCount_lt (file : FileState) (page : Page) (i : Nat) :
    i < presentCount file page ↔ i < page.size ∧ page.offset + i < file.bytes.length := by
  unfold presentCount
  rw [Nat.lt_min]
  omega

theorem presentCount_eq_of_agreement {before after : FileState} (page : Page)
    (agrees : AgreesOnPage before after page) :
    presentCount before page = presentCount after page := by
  have threshold (i : Nat) (inside : i < page.size) :
      i < presentCount before page ↔ i < presentCount after page := by
    rw [presentCount_lt, presentCount_lt]
    simp only [inside, true_and]
    have missing :
        before.bytes.length ≤ page.offset + i ↔ after.bytes.length ≤ page.offset + i := by
      calc
        _ ↔ before.bytes[page.offset + i]? = none := List.getElem?_eq_none_iff.symm
        _ ↔ after.bytes[page.offset + i]? = none := by rw [agrees i inside]
        _ ↔ _ := List.getElem?_eq_none_iff
    omega
  have beforeLe : presentCount before page ≤ page.size := Nat.min_le_left _ _
  have afterLe : presentCount after page ≤ page.size := Nat.min_le_left _ _
  by_cases equal : presentCount before page = presentCount after page
  · exact equal
  · have order : presentCount before page < presentCount after page ∨
        presentCount after page < presentCount before page := by omega
    rcases order with increasing | decreasing
    · have atCut := threshold (presentCount before page) (by omega)
      omega
    · have atCut := threshold (presentCount after page) (by omega)
      omega

/-- A successful disjoint write keeps the optional page bytes exactly when
it leaves the available prefix length within the requested interval equal. -/
theorem disjoint_write_agrees_iff {capacity : Nat} {before after : FileState} (page : Page)
    {offset : Int} {data : Bytes}
    (write : readWrite capacity before (.write page.handle offset data) = (.ok (), after))
    (apart : page.offset + page.size ≤ offset.toNat ∨ offset.toNat + data.length ≤ page.offset) :
    AgreesOnPage before after page ↔ presentCount before page = presentCount after page := by
  refine ⟨presentCount_eq_of_agreement page, ?_⟩
  intro count i inside
  by_cases present : page.offset + i < before.bytes.length
  · let bytePage : Page := ⟨page.handle, page.offset + i + 1, 1⟩
    have offsetExact : bytePage.offset = page.offset + i := by simp [bytePage, Page.offset]
    have complete : bytePage.offset + bytePage.size ≤ before.bytes.length := by
      change bytePage.offset + 1 ≤ before.bytes.length
      omega
    have apartByte : bytePage.offset + bytePage.size ≤ offset.toNat ∨
        offset.toNat + data.length ≤ bytePage.offset := by
      change bytePage.offset + 1 ≤ offset.toNat ∨ offset.toNat + data.length ≤ bytePage.offset
      omega
    have withinByte : 0 < bytePage.size := by
      change 0 < 1
      decide
    have framed := (MutationFrame.write_preserves_page bytePage write complete apartByte).1 0 withinByte
    simpa only [offsetExact, Nat.add_zero] using framed
  · have missingAfter : ¬ page.offset + i < after.bytes.length := by
      intro afterPresent
      have inPrefix := (presentCount_lt after page i).mpr ⟨inside, afterPresent⟩
      rw [← count] at inPrefix
      exact present ((presentCount_lt before page i).mp inPrefix).2
    rw [List.getElem?_eq_none_iff.mpr (by omega : before.bytes.length ≤ page.offset + i),
      List.getElem?_eq_none_iff.mpr (by omega : after.bytes.length ≤ page.offset + i)]

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.WriteExtent
