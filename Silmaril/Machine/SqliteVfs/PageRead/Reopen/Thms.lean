module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.Reopen.Retire

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.Reopen

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- Closing a live handle and reopening read-only advances the generation.
A fill using the retired handle records the rejection and preserves its
input cache. The three exchanges form a valid trace. -/
theorem stale_fill_after_reopen {State : Type} {handler : Handler State}
    {view : State → FileState} {maximumMode : Mode} (handles : HandleLaw maximumMode handler view)
    (reads : ReadLaw handler view) (before : State) (cache : Cache)
    (target : SlotId) (page : Page) (live : ((view before).mode page.handle).isNone = false)
    (owned : cache target = some .vacant) (admitted : page.Admitted) :
    let closed := (handler before (.close page.handle)).2
    let opened := (handler closed (.openFile .readOnly)).2
    let renewed : Handle := ⟨(view before).generation + 1⟩
    let stale := fill handler opened cache target page
    stale = ⟨.error (.vfs .invalidHandle), (handler opened page.request).2, cache,
        [⟨page.request, .error .invalidHandle⟩]⟩ ∧
      view stale.file = { view before with openMode := some .readOnly, generation := renewed.generation } ∧
      Trace.Valid handler before
        [⟨.close page.handle, .ok ()⟩, ⟨.openFile .readOnly, .ok renewed⟩,
          ⟨page.request, .error .invalidHandle⟩] stale.file :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.Reopen.stale_fill_after_reopen handles reads before cache target page live owned admitted

end Silmaril.Machine.SqliteVfs.PageRead.Reopen
