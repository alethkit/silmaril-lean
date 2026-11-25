module

public import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Defs
import Silmaril.Machine.SqliteVfs.PageRead.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.Acquire

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.Acquire (acquire)

theorem acquire_trace {State : Type} (handler : Handler State) (file : State)
    (cache : Cache) (target : SlotId) (page : Page) :
    let outcome := acquire handler file cache target page
    Trace.Valid handler file outcome.trace outcome.file := by
  cases hit : CacheHit.lookup cache target page with
  | none => simpa [acquire, hit] using fill_trace handler file cache target page
  | some bytes =>
    simp only [acquire, hit]
    exact .nil file

theorem readOnly_cold_warm (capacity : Nat) (file : FileState) (cache : Cache)
    (target : SlotId) (page : Page) (owned : cache target = some .vacant)
    (admitted : page.Admitted) (live : (file.mode page.handle).isNone = false)
    (complete : page.offset + page.size ≤ file.bytes.length) :
    let bytes := readBytes file.bytes page.offset page.size
    let cold := acquire (readOnly capacity) file cache target page
    let warm := acquire (readOnly capacity) cold.file cold.cache target page
    cold = ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ ∧
      warm = ⟨.ok bytes, cold.file, cold.cache, []⟩ ∧
      Trace.Valid (readOnly capacity) file (cold.trace ++ warm.trace) warm.file := by
  have miss : CacheHit.lookup cache target page = none := by simp [CacheHit.lookup, owned]
  have fillEq := readOnly_fill capacity file cache target page owned admitted live
  dsimp only at fillEq
  rw [ite_eq_left complete] at fillEq
  have missEq : acquire (readOnly capacity) file cache target page =
      fill (readOnly capacity) file cache target page := by
    simp [acquire, miss]
  have cold := missEq.trans fillEq
  have hit : CacheHit.lookup (cache.install target page (readBytes file.bytes page.offset page.size))
      target page = some (readBytes file.bytes page.offset page.size) := by
    simp [CacheHit.lookup, Cache.install]
  have valid := acquire_trace (readOnly capacity) file cache target page
  dsimp only at valid ⊢
  rw [cold] at valid ⊢
  simpa [acquire, hit] using valid

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.Acquire
