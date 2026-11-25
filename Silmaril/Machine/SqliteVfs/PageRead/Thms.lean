module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.Fill

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead

variable {State : Type} (handler : Handler State) (file : State) (cache : Cache)
  (target : SlotId) (page : Page)

/-- The lower-level observation is a valid VFS trace, with the actual end state. -/
theorem fill_trace :
    let after := fill handler file cache target page
    Trace.Valid handler file after.trace after.file :=
  Proofs.Machine.SqliteVfs.PageRead.fill_trace handler file cache target page

/-- A fill frames every slot except its target. -/
theorem fill_other (slot : SlotId) (different : slot ≠ target) :
    (fill handler file cache target page).cache slot = cache slot :=
  Proofs.Machine.SqliteVfs.PageRead.fill_other handler file cache target page slot different

/-- Any rejected fill preserves the entire input cache. -/
theorem fill_rejected {reason : FillError}
    (rejected : (fill handler file cache target page).result = .error reason) :
    (fill handler file cache target page).cache = cache :=
  Proofs.Machine.SqliteVfs.PageRead.fill_rejected handler file cache target page rejected

/-- A successful fill consumes exactly the target's vacancy and installs the returned bytes. -/
theorem fill_success {bytes : Bytes}
    (success : (fill handler file cache target page).result = .ok bytes) :
    cache target = some .vacant ∧ page.Admitted ∧
      (fill handler file cache target page).cache target = some (.resident page bytes) :=
  Proofs.Machine.SqliteVfs.PageRead.fill_success handler file cache target page success

/-- With an available slot, an admitted address, and a live handle, a bounded
read-only backing installs the exact complete page or records a short read
while leaving the slot vacant. Both replies expose the original file buffer. -/
theorem readOnly_fill (capacity : Nat) (file : FileState) (cache : Cache)
    (target : SlotId) (page : Page) (owned : cache target = some .vacant)
    (admitted : page.Admitted) (live : (file.mode page.handle).isNone = false) :
    let bytes := readBytes file.bytes page.offset page.size
    if page.offset + page.size ≤ file.bytes.length then
      fill (readOnly capacity) file cache target page =
        ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩
    else
      fill (readOnly capacity) file cache target page =
        ⟨.error .shortRead, file, cache, [⟨page.request, .shortRead bytes⟩]⟩ :=
  Proofs.Machine.SqliteVfs.PageRead.readOnly_fill capacity file cache target page owned admitted live

end Silmaril.Machine.SqliteVfs.PageRead
