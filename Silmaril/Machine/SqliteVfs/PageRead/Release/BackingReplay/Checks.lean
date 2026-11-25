module

import Silmaril.Machine.SqliteVfs.PageRead.Release.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.Release.BackingReplay

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def initial : FileState := ⟨[10, 20], some .readOnly, 0⟩
private def updated : FileState := ⟨[30, 40], some .readOnly, 1⟩
private def firstPage : Page := ⟨⟨0⟩, 1, 2⟩
private def nextPage : Page := ⟨⟨1⟩, 1, 2⟩
private def cache : Cache := fun slot =>
  if slot = 0 then some .vacant else if slot = 1 then some (.resident firstPage [10, 20]) else none

/-- The first read returns the old bytes and advances the backing state. -/
private def updating : Handler FileState := fun file request =>
  match request with
  | .read handle offset count =>
    if file.generation = 0 ∧ handle = firstPage.handle ∧ offset = 0 ∧ count = 2 then
      (.ok [10, 20], updated)
    else readOnly 8 file (.read handle offset count)
  | other => readOnly 8 file other

private theorem state_changing_release_replay :
    let first := fill updating initial cache 0 firstPage
    let next := fill updating first.file cache 0 nextPage
    let expected : Trace := [⟨firstPage.request, .ok [10, 20]⟩, ⟨nextPage.request, .ok [30, 40]⟩]
    release first.cache 0 firstPage = .ok cache ∧
      first.file = updated ∧ next.file = updated ∧
      next.result = .ok [30, 40] ∧
      next.cache 0 = some (.resident nextPage [30, 40]) ∧
      next.cache 1 = some (.resident firstPage [10, 20]) ∧
      first.trace ++ next.trace = expected ∧ Trace.Valid updating initial expected next.file := by
  refine ⟨release_after_fill_success updating initial cache 0 firstPage
    (bytes := [10, 20]) rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact .cons rfl (.cons rfl (.nil updated))

#print axioms state_changing_release_replay

end Silmaril.Machine.SqliteVfs.PageRead.Release.BackingReplay
