module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.CacheHit.Refetch

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.CacheHit

open Silmaril.Formats.Sqlite

/-- Looking up the page just installed by a successful fill returns its bytes. -/
theorem lookup_after_success {State : Type} (handler : Handler State) (file : State)
    (cache : Cache) (target : SlotId) (page : Page) {bytes : Bytes}
    (success : (fill handler file cache target page).result = .ok bytes) :
    lookup (fill handler file cache target page).cache target page = some bytes :=
  Proofs.Machine.SqliteVfs.PageRead.CacheHit.lookup_after_success handler file cache target page success

/-- A hit from the original fill returns the exact read-only refetch buffer
when the page interval still agrees. The reference fill uses the same
vacant starting slot in the current snapshot. -/
theorem hit_after_fill_matches_refetch (capacity : Nat) (before current : FileState) (cache : Cache)
    (target : SlotId) (page : Page) (owned : cache target = some .vacant)
    (admitted : page.Admitted) (beforeLive : (before.mode page.handle).isNone = false)
    (currentLive : (current.mode page.handle).isNone = false)
    (beforeFits : page.offset + page.size ≤ before.bytes.length)
    (agrees : AgreesOnPage before current page) :
    let original := fill (readOnly capacity) before cache target page
    let fresh := fill (readOnly capacity) current cache target page
    ∃ bytes, lookup original.cache target page = some bytes ∧
      fresh = ⟨.ok bytes, current, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ :=
  Proofs.Machine.SqliteVfs.PageRead.CacheHit.hit_after_fill_matches_refetch capacity
    before current cache target page owned admitted beforeLive currentLive beforeFits agrees

/-- Cache lookup and the valid reference refetch give the same optional
designated-root VDBE result for every common program input. Only the
reference refetch performs a VFS operation. -/
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
          runPage? fresh.result.toOption base db root program fuel initial :=
  Proofs.Machine.SqliteVfs.PageRead.CacheHit.runHit_matches_refetch capacity
    before current cache target page owned admitted beforeLive currentLive beforeFits agrees

end Silmaril.Machine.SqliteVfs.PageRead.CacheHit
