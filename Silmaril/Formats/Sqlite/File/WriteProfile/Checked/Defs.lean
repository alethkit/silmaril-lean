module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs

@[expose] public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image.Checked

inductive Error where
  | encode (error : Image.Error)
  | readback
  | rowsMismatch
  deriving DecidableEq, Repr

/-- Read the serialized catalogue and data leaves before returning the image.
The read path validates physical layout and reconstructs the rowid alias. -/
def encode (snapshot : Snapshot) : Except Error Bytes :=
  match Image.encode snapshot with
  | .error error => .error (.encode error)
  | .ok bytes =>
    match TableLeaf.open? bytes with
    | none => .error .readback
    | some table =>
      if table.entries = snapshot.readTable.entries then .ok bytes else .error .rowsMismatch

end Silmaril.Formats.Sqlite.WriteProfile.Image.Checked
