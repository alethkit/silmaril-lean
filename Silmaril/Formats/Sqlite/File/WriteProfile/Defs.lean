module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.WriteProfile.Defs

/-! A fresh two-page database. Page 1 contains the catalogue record; page 2
contains the rowid-ordered committed or explicitly supplied logical snapshot. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.WriteProfile.Image

inductive Error where
  | schemaPage (error : BTree.LeafWrite.Error)
  | tablePage (error : BTree.LeafWrite.Error)
  deriving DecidableEq, Repr

def cataloguePage : Except BTree.LeafWrite.Error (List UInt8) :=
  BTree.LeafWrite.encode File.Write.header [⟨1, Record.Write.schema⟩]

def tablePage (snapshot : Snapshot) : Except BTree.LeafWrite.Error (List UInt8) :=
  BTree.LeafWrite.encode []
    (snapshot.orderedRows.map fun row => ⟨row.id, Record.Write.amount row.amount⟩)

def encode (snapshot : Snapshot) : Except Error Bytes :=
  match cataloguePage, tablePage snapshot with
  | .error error, _ => .error (.schemaPage error)
  | .ok _, .error error => .error (.tablePage error)
  | .ok catalogue, .ok rows => .ok (Silmaril.Formats.Bytes.ofList (catalogue ++ rows))

end Silmaril.Formats.Sqlite.WriteProfile.Image
