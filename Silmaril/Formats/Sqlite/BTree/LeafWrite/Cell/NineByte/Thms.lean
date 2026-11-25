module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.NineByte.Roundtrip

public section
namespace Silmaril.Formats.Sqlite.BTree.LeafWrite.Cell

/-- For a key with a nine-octet SQLite varint, the materialized amount cell
recovers its exact typed row and occupies 21 bytes at offset zero. -/
theorem amount_roundtrip_nine (key amount : Int64) (high : 2 ^ 56 ≤ key.toUInt64.toNat) :
    let cell : Cell := ⟨key, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    TableLeaf.cell? view 0 = some ⟨key, Bytes.ofList (Record.Write.amount amount), 0, 21⟩ ∧
    (TableLeaf.cell? view 0).bind TableLeaf.row? =
      some (key.toInt, [.integer key, .integer amount]) :=
  Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.NineByte.amount_roundtrip_nine key amount high

/-- Every negative signed rowid uses the nine-octet key encoding. -/
theorem amount_roundtrip_negative (key amount : Int64) (negative : key.toInt < 0) :
    let cell : Cell := ⟨key, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    TableLeaf.cell? view 0 = some ⟨key, Bytes.ofList (Record.Write.amount amount), 0, 21⟩ ∧
    (TableLeaf.cell? view 0).bind TableLeaf.row? =
      some (key.toInt, [.integer key, .integer amount]) :=
  Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.NineByte.amount_roundtrip_negative key amount negative

end Silmaril.Formats.Sqlite.BTree.LeafWrite.Cell
