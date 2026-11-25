module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

variable {State : Type} (handler : Handler State) (file : State) (cache : Cache)
  (target : SlotId) (page : Page)

theorem fill_trace :
    let after := fill handler file cache target page
    Trace.Valid handler file after.trace after.file := by
  unfold fill
  split
  · split
    · split
      next reply after step => exact .cons step (.nil _)
    · exact .nil _
  · exact .nil _

theorem fill_other (slot : SlotId) (different : slot ≠ target) :
    (fill handler file cache target page).cache slot = cache slot := by
  unfold fill
  split
  · split
    · split
      next reply after step =>
        cases accept page.size reply <;> simp [Cache.install, different]
    · rfl
  · rfl

theorem fill_rejected {reason : FillError}
    (rejected : (fill handler file cache target page).result = .error reason) :
    (fill handler file cache target page).cache = cache := by
  revert rejected
  unfold fill
  split
  · split
    · split
      next reply after step => cases accept page.size reply <;> simp
    · exact fun _ => rfl
  · exact fun _ => rfl

theorem fill_success {bytes : Bytes}
    (success : (fill handler file cache target page).result = .ok bytes) :
    cache target = some .vacant ∧ page.Admitted ∧
      (fill handler file cache target page).cache target = some (.resident page bytes) := by
  revert success
  unfold fill
  split
  · next owned =>
    split
    · next admitted =>
      split
      next reply after step =>
        cases accept page.size reply with
        | error reason => simp
        | ok contents =>
          intro success
          simp only [Except.ok.injEq] at success
          subst contents
          exact ⟨owned, admitted, by simp [Cache.install]⟩
    · simp
  · simp

theorem readOnly_fill (capacity : Nat) (file : FileState) (cache : Cache)
    (target : SlotId) (page : Page) (owned : cache target = some .vacant)
    (admitted : page.Admitted) (live : (file.mode page.handle).isNone = false) :
    let bytes := readBytes file.bytes page.offset page.size
    if page.offset + page.size ≤ file.bytes.length then
      fill (readOnly capacity) file cache target page =
        ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩
    else
      fill (readOnly capacity) file cache target page =
        ⟨.error .shortRead, file, cache, [⟨page.request, .shortRead bytes⟩]⟩ := by
  have range := admitted.2
  have length : (readBytes file.bytes page.offset page.size).length = page.size := by simp [readBytes]
  by_cases complete : page.offset + page.size ≤ file.bytes.length <;>
    simp [fill, owned, admitted, Page.request, backing, live, range, readBacking, accept, complete, length]

end Silmaril.Proofs.Machine.SqliteVfs.PageRead
