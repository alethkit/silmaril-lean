module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.SizedFill.Compose

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.SizedFill

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- A successful size reply bounds a full fill when the requested page
fits the reported extent. The fill starts from the actual state returned by
the size call, and both VFS operations preserve the file view. -/
theorem size_then_full_fill {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadLaw step view) (start : State) (cache : Cache) (target : SlotId)
    (page : Page) (reportedSize : Nat)
    (observed : (step start (.fileSize page.handle)).1 = .ok reportedSize)
    (fits : page.offset + page.size ≤ reportedSize) (owned : cache target = some .vacant)
    (admitted : page.Admitted) :
    let sized := (step start (.fileSize page.handle)).2
    let bytes := readBytes (view start).bytes page.offset page.size
    let outcome := fill step sized cache target page
    (view sized = view start ∧ (view sized).bytes.length = reportedSize ∧
        ((view sized).mode page.handle).isNone = false) ∧
      outcome = ⟨.ok bytes, (step sized page.request).2, cache.install target page bytes,
        [⟨page.request, .ok bytes⟩]⟩ ∧
      view outcome.file = view start ∧
      Trace.Valid step start [⟨.fileSize page.handle, .ok reportedSize⟩, ⟨page.request, .ok bytes⟩] outcome.file :=
  Silmaril.Proofs.Machine.SqliteVfs.PageRead.SizedFill.size_then_full_fill law start cache target page reportedSize
    observed fits owned admitted

end Silmaril.Machine.SqliteVfs.PageRead.SizedFill
