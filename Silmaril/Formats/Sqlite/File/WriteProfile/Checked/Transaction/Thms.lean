module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Transaction.Pending

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image.Checked

/-- A successful edit within a logical transaction preserves the committed
encoder result and selects the edited encoder result for the pending view.
Logical commit keeps the edited result and rollback recovers the original. -/
theorem pending_edit_images (state : State) {before : Snapshot} {edit : Edit} {after : Edited}
    (pending : state.pending = some before) (accepted : before.apply edit = .ok after) :
    let updated := (step state (.edit edit)).state
    encode updated.committed = encode state.committed ∧
    encode updated.visible = encode after.snapshot ∧
    encode (step updated .commit).state.visible = encode after.snapshot ∧
    encode (step updated .rollback).state.visible = encode state.committed :=
  Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Transaction.pending_edit_images
    state pending accepted

end Silmaril.Formats.Sqlite.WriteProfile.Image.Checked
