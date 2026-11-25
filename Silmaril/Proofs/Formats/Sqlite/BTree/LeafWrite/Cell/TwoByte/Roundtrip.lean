module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.Amount.Roundtrip
import Silmaril.Formats.Sqlite.Varint.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.TwoByte

private theorem key_width_two (value : UInt64) (lo : 128 ≤ value.toNat)
    (hi : value.toNat < 16384) : (Varint.encode value).toList.length = 2 := by
  have short : value.toNat < 2 ^ 56 := by omega
  have highOctet : value.toNat / 128 < 128 := by omega
  unfold Varint.encode
  rw [ite_eq_left short, Bytes.toList_ofList, Varint.seven, ite_eq_right (by omega),
    Varint.seven, ite_eq_left highOctet]
  rfl

theorem amount_roundtrip_two (key amount : Int64) (lo : 128 ≤ key.toUInt64.toNat)
    (hi : key.toUInt64.toNat < 16384) :
    let cell : BTree.LeafWrite.Cell := ⟨key, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    TableLeaf.cell? view 0 = some ⟨key, Bytes.ofList (Record.Write.amount amount), 0, 14⟩ ∧
    (TableLeaf.cell? view 0).bind TableLeaf.row? =
      some (key.toInt, [.integer key, .integer amount]) := by
  let digits := (Varint.encode key.toUInt64).toList
  have width : digits.length = 2 := key_width_two key.toUInt64 lo hi
  have parsed := Varint.read?_encode_two _ 1 key.toUInt64 lo hi fun i inside =>
    Amount.encoded_key_byte key amount i (by
      change i < digits.length
      rw [width]
      exact inside)
  have input : Varint.read? (File.View.ofBytes (Bytes.ofList
      (BTree.LeafWrite.Cell.bytes ⟨key, Record.Write.amount amount⟩))) 1 =
      some (key.toUInt64, 1 + digits.length) := by
    rw [width]
    exact parsed
  have row := Amount.amount_roundtrip_of_key key amount input
  change _ ∧ _ at row
  simpa [show (Varint.encode key.toUInt64).toList.length = 2 from width] using row

end Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.TwoByte
