module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Machine.SqliteVfs.PageRead.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.CacheHit

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit
open Silmaril.Formats.Sqlite

private theorem equalReadBytes {before current : FileState} {page : Page}
    (agrees : AgreesOnPage before current page) :
    readBytes before.bytes page.offset page.size = readBytes current.bytes page.offset page.size := by
  unfold readBytes
  congr 1
  funext i
  rw [agrees i.val i.isLt]

private theorem complete_of_agreement {before current : FileState} {page : Page}
    (positive : 0 < page.size) (beforeFits : page.offset + page.size ≤ before.bytes.length)
    (agrees : AgreesOnPage before current page) :
    page.offset + page.size ≤ current.bytes.length := by
  apply Nat.le_of_not_gt
  intro short
  have inside : page.size - 1 < page.size := by omega
  have missing : current.bytes[page.offset + (page.size - 1)]? = none :=
    List.getElem?_eq_none_iff.mpr (by omega)
  have first := agrees (page.size - 1) inside
  rw [missing, List.getElem?_eq_none_iff] at first
  omega

theorem lookup_after_success {State : Type} (handler : Handler State) (file : State)
    (cache : Cache) (target : SlotId) (page : Page) {bytes : Bytes}
    (success : (fill handler file cache target page).result = .ok bytes) :
    lookup (fill handler file cache target page).cache target page = some bytes := by
  have installed := (fill_success handler file cache target page success).2.2
  simp [lookup, installed]

theorem hit_after_fill_matches_refetch (capacity : Nat) (before current : FileState) (cache : Cache)
    (target : SlotId) (page : Page) (owned : cache target = some .vacant)
    (admitted : page.Admitted) (beforeLive : (before.mode page.handle).isNone = false)
    (currentLive : (current.mode page.handle).isNone = false)
    (beforeFits : page.offset + page.size ≤ before.bytes.length)
    (agrees : AgreesOnPage before current page) :
    let original := fill (readOnly capacity) before cache target page
    let fresh := fill (readOnly capacity) current cache target page
    ∃ bytes, lookup original.cache target page = some bytes ∧
      fresh = ⟨.ok bytes, current, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ := by
  have installation := (ite_eq_left beforeFits).mp
    (readOnly_fill capacity before cache target page owned admitted beforeLive)
  have positive : 0 < page.size := by
    have count := admitted.2.2.1
    change 0 < (page.size : Int) at count
    omega
  have currentFits := complete_of_agreement positive beforeFits agrees
  have refetch := (ite_eq_left currentFits).mp
    (readOnly_fill capacity current cache target page owned admitted currentLive)
  refine ⟨readBytes before.bytes page.offset page.size, ?_, ?_⟩
  · apply lookup_after_success
    rw [installation]
  · rw [equalReadBytes agrees]
    exact refetch

theorem runHit_matches_refetch (capacity : Nat) (before current : FileState) (cache : Cache)
    (target : SlotId) (page : Page) (owned : cache target = some .vacant)
    (admitted : page.Admitted) (beforeLive : (before.mode page.handle).isNone = false)
    (currentLive : (current.mode page.handle).isNone = false)
    (beforeFits : page.offset + page.size ≤ before.bytes.length)
    (agrees : AgreesOnPage before current page) :
    let original := fill (readOnly capacity) before cache target page
    let fresh := fill (readOnly capacity) current cache target page
    Trace.Valid (readOnly capacity) current fresh.trace current ∧
      ∀ (base db root : Nat) (program : Vdbe.Program) (fuel : Nat) (initial : Vdbe.State),
        runHit? original.cache target page base db root program fuel initial =
          runPage? fresh.result.toOption base db root program fuel initial := by
  obtain ⟨bytes, hit, fresh⟩ :=
    hit_after_fill_matches_refetch capacity before current cache target page owned admitted
      beforeLive currentLive beforeFits agrees
  have valid := fill_trace (readOnly capacity) current cache target page
  dsimp only at valid ⊢
  rw [fresh] at valid ⊢
  refine ⟨valid, fun base db root program fuel initial => ?_⟩
  unfold runHit?
  rw [hit]
  rfl

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.CacheHit
