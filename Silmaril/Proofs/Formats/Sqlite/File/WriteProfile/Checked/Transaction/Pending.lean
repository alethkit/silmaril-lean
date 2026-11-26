module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Formats.Sqlite.WriteProfile.Thms

public section

open Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Transaction

open WriteProfile

theorem pending_edit_images (state : State) {before : Snapshot} {edit : Edit} {after : Edited}
    (pending : state.pending = some before) (accepted : before.apply edit = .ok after) :
    let updated := (step state (.edit edit)).state
    Image.Checked.encode updated.committed = Image.Checked.encode state.committed ∧
    Image.Checked.encode updated.visible = Image.Checked.encode after.snapshot ∧
    Image.Checked.encode (step updated .commit).state.visible = Image.Checked.encode after.snapshot ∧
    Image.Checked.encode (step updated .rollback).state.visible = Image.Checked.encode state.committed := by
  dsimp only
  rw [pending_edit state pending accepted]
  rw [commit _ rfl, rollback _ rfl]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Transaction
