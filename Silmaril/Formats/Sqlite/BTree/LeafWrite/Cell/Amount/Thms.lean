module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.Amount.Read

public section
namespace Silmaril.Formats.Sqlite.BTree.LeafWrite.Cell

/-- The serialized amount cell at offset zero recovers every signed key and
amount. The exact stop offset includes the key's actual encoded length. -/
theorem amount_roundtrip (key amount : Int64) :
    let cell : Cell := ⟨key, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    let stop := 1 + (Varint.encode key.toUInt64).toList.length + 11
    TableLeaf.cell? view 0 = some ⟨key, Bytes.ofList (Record.Write.amount amount), 0, stop⟩ ∧
    (TableLeaf.cell? view 0).bind TableLeaf.row? =
      some (key.toInt, [.integer key, .integer amount]) :=
  Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.Amount.amount_roundtrip key amount

end Silmaril.Formats.Sqlite.BTree.LeafWrite.Cell
