module

public import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.Acquire.Trace

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.Acquire

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- A hit supplies the exact stored bytes and preserves the file and cache. -/
theorem acquire_hit {State : Type} (handler : Handler State) (file : State)
    (cache : Cache) (target : SlotId) (page : Page) {bytes : Bytes}
    (hit : CacheHit.lookup cache target page = some bytes) :
    acquire handler file cache target page = ⟨.ok bytes, file, cache, []⟩ := by
  simp [acquire, hit]

/-- A miss uses the full existing fill operation, including its rejection paths. -/
theorem acquire_miss {State : Type} (handler : Handler State) (file : State)
    (cache : Cache) (target : SlotId) (page : Page)
    (miss : CacheHit.lookup cache target page = none) :
    acquire handler file cache target page = fill handler file cache target page := by
  simp [acquire, miss]

/-- The acquisition's recorded exchanges are valid for its actual file transition. -/
theorem acquire_trace {State : Type} (handler : Handler State) (file : State)
    (cache : Cache) (target : SlotId) (page : Page) :
    let outcome := acquire handler file cache target page
    Trace.Valid handler file outcome.trace outcome.file :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.Acquire.acquire_trace handler file cache target page

/-- The cold call installs the full page. A second call using its returned
file and cache supplies the same bytes with no second read. -/
theorem readOnly_cold_warm (capacity : Nat) (file : FileState) (cache : Cache)
    (target : SlotId) (page : Page) (owned : cache target = some .vacant)
    (admitted : page.Admitted) (live : (file.mode page.handle).isNone = false)
    (complete : page.offset + page.size ≤ file.bytes.length) :
    let bytes := readBytes file.bytes page.offset page.size
    let cold := acquire (readOnly capacity) file cache target page
    let warm := acquire (readOnly capacity) cold.file cold.cache target page
    cold = ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ ∧
      warm = ⟨.ok bytes, cold.file, cold.cache, []⟩ ∧
      Trace.Valid (readOnly capacity) file (cold.trace ++ warm.trace) warm.file :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.Acquire.readOnly_cold_warm capacity file cache target page owned admitted live complete

end Silmaril.Machine.SqliteVfs.PageRead.Acquire
