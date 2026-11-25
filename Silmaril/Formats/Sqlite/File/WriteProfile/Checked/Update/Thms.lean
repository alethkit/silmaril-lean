module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Checked.Defs
import Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Update.Capacity

public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image.Checked

/-- A successful amount update preserves the capacity of the fixed write
profile. Each fitting snapshot has its own exact reopened image, and an
overfull snapshot keeps the same typed capacity error. -/
theorem update_preserves_image_capacity {snapshot : Snapshot} {id : Int64}
    {amount : Option Int64} {edited : Edited} (updated : snapshot.update id amount = .ok edited) :
    ((∃ bytes, encode snapshot = .ok bytes ∧ bytes.length = 1024 ∧
       TableLeaf.open? bytes = some snapshot.readTable) ↔
     (∃ bytes, encode edited.snapshot = .ok bytes ∧ bytes.length = 1024 ∧
       TableLeaf.open? bytes = some edited.snapshot.readTable)) ∧
    (encode snapshot = .error (.encode (.tablePage .pageFull)) ↔
     encode edited.snapshot = .error (.encode (.tablePage .pageFull))) :=
  Silmaril.Proofs.Formats.Sqlite.File.WriteProfile.Checked.Update.update_preserves_image_capacity updated

end Silmaril.Formats.Sqlite.WriteProfile.Image.Checked
