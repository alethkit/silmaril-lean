module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Formats.Sqlite.Varint.Exact.Thms
import Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.Amount.Roundtrip

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.Amount

/-- An amount cell reconstructs every signed rowid and amount at offset zero.
The encoded key extent determines the original cell's stop offset. -/
theorem amount_roundtrip (key amount : Int64) :
    let cell : BTree.LeafWrite.Cell := ⟨key, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    let stop := 1 + (Varint.encode key.toUInt64).toList.length + 11
    TableLeaf.cell? view 0 = some ⟨key, Bytes.ofList (Record.Write.amount amount), 0, stop⟩ ∧
    (TableLeaf.cell? view 0).bind TableLeaf.row? =
      some (key.toInt, [.integer key, .integer amount]) := by
  apply amount_roundtrip_of_key key amount
  exact Varint.read?_encode _ 1 key.toUInt64
    (encoded_key_byte key amount)

end Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.Amount
