module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.Reopen

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

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
          ⟨page.request, .error .invalidHandle⟩] stale.file := by
  dsimp only
  let closed := (handler before (.close page.handle)).2
  let opened := (handler closed (.openFile .readOnly)).2
  let renewed : Handle := ⟨(view before).generation + 1⟩
  have closedResult : (handler before (.close page.handle)).1 = .ok () ∧
      view closed = { view before with openMode := none, generation := (view before).generation + 1 } := by
    simpa [closed, live] using handles.close before page.handle
  have openedResult : (handler closed (.openFile .readOnly)).1 = .ok renewed ∧
      view opened = { view before with openMode := some .readOnly, generation := renewed.generation } := by
    simpa [opened, closedResult.2, renewed] using handles.openFile closed .readOnly
  have oldGeneration : page.handle.generation = (view before).generation := by
    by_cases same : page.handle.generation = (view before).generation
    · exact same
    · simp [FileState.mode, same] at live
  have retired : ((view opened).mode page.handle).isNone = true := by
    simp [FileState.mode, openedResult.2, oldGeneration, renewed]
  let after := (handler opened page.request).2
  have staleResult : (handler opened page.request).1 = .error .invalidHandle ∧
      view after = view opened := by
    have law := reads.read opened page.handle page.offset page.size
    have observed : view after = view opened ∧
        (handler opened page.request).1 = .error .invalidHandle := by
      simpa [after, Page.request, retired] using law
    exact observed.symm
  have staleStep : handler opened page.request = (.error .invalidHandle, after) :=
    Prod.ext staleResult.1 rfl
  have staleFill :
      fill handler opened cache target page = ⟨.error (.vfs .invalidHandle), after, cache,
        [⟨page.request, .error .invalidHandle⟩]⟩ := by
    simp [fill, owned, admitted, staleStep, accept]
  change fill handler opened cache target page = _ ∧ _
  rw [staleFill]
  exact ⟨rfl, staleResult.2.trans openedResult.2,
    .cons (Prod.ext closedResult.1 rfl)
      (.cons (Prod.ext openedResult.1 rfl) (.cons staleStep (.nil after)))⟩

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.Reopen
