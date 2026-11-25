module
public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
import Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Header

public section
namespace Silmaril.Formats.Sqlite.BTree.LeafWrite

/-- A successful layout stores the input cell count and first content offset
in the two header fields after the leading bytes. Success implies both values
fit in the two-byte fields. Offsets are relative to the serialized page. -/
theorem layout_header_fields {leading page : List UInt8} {cells : List (List UInt8)}
    (accepted : layout leading cells = .ok page) :
    let view := File.View.ofBytes (Bytes.ofList page)
    view.be? (leading.length + 3) 2 = some cells.length ∧
      view.be? (leading.length + 5) 2 =
        some (File.Write.pageSize - cells.flatten.length) :=
  Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.layout_header_fields accepted

/-- An in-range pointer slot of a successful layout stores the content start
plus the byte lengths of the preceding serialized cells. The field starts at
the shown offset relative to the serialized page, including its leading bytes. -/
theorem layout_pointer {leading page : List UInt8} {cells : List (List UInt8)} (slot : Nat)
    (accepted : layout leading cells = .ok page) (within : slot < cells.length) :
    let view := File.View.ofBytes (Bytes.ofList page)
    view.be? (leading.length + 8 + 2 * slot) 2 =
      some (File.Write.pageSize - cells.flatten.length + (cells.take slot).flatten.length) :=
  Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.layout_pointer slot accepted within

end Silmaril.Formats.Sqlite.BTree.LeafWrite
