module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Machine.SqliteVfs.PageRead.ReadFrame.Thms
import Silmaril.Machine.SqliteVfs.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.SizedFill

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

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
      Trace.Valid step start [⟨.fileSize page.handle, .ok reportedSize⟩, ⟨page.request, .ok bytes⟩] outcome.file := by
  dsimp only
  let sized := (step start (.fileSize page.handle)).2
  let bytes := readBytes (view start).bytes page.offset page.size
  let after := (step sized page.request).2
  have sizeLaw := law.fileSize start page.handle
  have sizeFrame : view sized = view start := sizeLaw.1
  have live : ((view start).mode page.handle).isNone = false := by
    cases dead : ((view start).mode page.handle).isNone with
    | false => rfl
    | true =>
      have result := sizeLaw.2
      simp [observed, dead] at result
  have sizeExact : reportedSize = (view start).bytes.length := by
    have result : (Except.ok reportedSize : Except Error Nat) = .ok (view start).bytes.length := by
      simpa only [observed, live, Bool.false_eq_true, ↓reduceIte, Response] using sizeLaw.2
    exact Except.ok.inj result
  have complete : page.offset + page.size ≤ (view start).bytes.length := sizeExact ▸ fits
  have liveAfter : ((view sized).mode page.handle).isNone = false := by
    simpa only [sizeFrame] using live
  have reference : (readOnly reportedSize (view start) page.request).1 = .ok bytes := by
    simp [Page.request, backing, readBacking, live, admitted.2, complete, bytes]
    rfl
  have agrees : CacheHit.AgreesOnPage (view sized) (view start) page := by
    rw [sizeFrame]
    exact fun _ _ => rfl
  have reply := (ReadFrame.lawful_read_reply_agrees law (readOnly_lawful reportedSize).2.1
    sized (view start) page admitted liveAfter live agrees).trans reference
  have readStep : step sized page.request = (.ok bytes, after) := Prod.ext reply rfl
  have readFrame : view after = view sized := by
    have result := (law.read sized page.handle page.offset page.size).1
    simpa [after, Page.request] using result
  have filled : fill step sized cache target page =
      ⟨.ok bytes, after, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ := by
    simp [fill, owned, admitted, readStep, accept, bytes, readBytes]
  have observedLength : (view sized).bytes.length = reportedSize := by
    rw [sizeFrame, sizeExact]
  change _ ∧ fill step sized cache target page = _ ∧ _
  rw [filled]
  exact ⟨⟨sizeFrame, observedLength, liveAfter⟩, rfl, readFrame.trans sizeFrame,
    .cons (Prod.ext observed rfl) (.cons readStep (.nil after))⟩

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.SizedFill
