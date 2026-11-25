module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
import Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Materialize.Slice

public section
namespace Silmaril.Formats.Sqlite.BTree.LeafWrite

/-- A pointer in a successful layout identifies the exact view of its
selected serialized cell. Materializing that view recovers the cell bytes. -/
theorem layout_pointer_materialize {leading page cell : List UInt8} {cells : List (List UInt8)}
    (slot : Nat) (accepted : layout leading cells = .ok page) (found : cells[slot]? = some cell) :
    let source := Bytes.ofList page
    let view := File.View.ofBytes source
    let offset := File.Write.pageSize - cells.flatten.length + (cells.take slot).flatten.length
    view.be? (leading.length + 8 + 2 * slot) 2 = some offset ∧
      ∃ part, view.sub? offset cell.length = some part ∧
        part.source = source ∧ part.start = offset ∧ part.length = cell.length ∧
        part.materialize = Bytes.ofList cell :=
  Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Materialize.layout_pointer_materialize
    slot accepted found

end Silmaril.Formats.Sqlite.BTree.LeafWrite
