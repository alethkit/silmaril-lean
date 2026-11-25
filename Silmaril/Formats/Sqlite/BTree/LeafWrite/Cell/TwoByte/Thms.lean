module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.TwoByte.Roundtrip

public section
namespace Silmaril.Formats.Sqlite.BTree.LeafWrite.Cell

/-- For a two-octet rowid and any signed amount, the actual cell and row
readers recover the exact 14-byte cell and typed row at offset zero. -/
theorem amount_roundtrip_two (key amount : Int64) (lo : 128 ≤ key.toUInt64.toNat)
    (hi : key.toUInt64.toNat < 16384) :
    let cell : Cell := ⟨key, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    TableLeaf.cell? view 0 = some ⟨key, Bytes.ofList (Record.Write.amount amount), 0, 14⟩ ∧
    (TableLeaf.cell? view 0).bind TableLeaf.row? =
      some (key.toInt, [.integer key, .integer amount]) :=
  Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.TwoByte.amount_roundtrip_two key amount lo hi

end Silmaril.Formats.Sqlite.BTree.LeafWrite.Cell
