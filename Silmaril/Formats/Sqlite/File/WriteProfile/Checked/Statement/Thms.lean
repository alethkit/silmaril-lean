module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Formats.Sqlite.WriteProfile.Thms

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image.Checked

/-- A rejected logical command preserves the complete checked encoder results
for the committed and visible snapshots, including bytes and typed errors. -/
theorem failed_statement_images (state : State) {command : Command} {error : WriteProfile.Error}
    (failed : (step state command).result = .error error) :
    let after := (step state command).state
    encode after.committed = encode state.committed ∧
    encode after.visible = encode state.visible := by
  dsimp only
  rw [error_preserves state failed]
  exact ⟨rfl, rfl⟩

end Silmaril.Formats.Sqlite.WriteProfile.Image.Checked
