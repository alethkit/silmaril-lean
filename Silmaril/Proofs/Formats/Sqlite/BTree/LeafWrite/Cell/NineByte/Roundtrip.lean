module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.Amount.Roundtrip
import Silmaril.Formats.Sqlite.Varint.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.NineByte

private theorem key_width_nine (value : UInt64) (high : 2 ^ 56 ≤ value.toNat) :
    (Varint.encode value).toList.length = 9 := by
  unfold Varint.encode
  rw [ite_eq_right (Nat.not_lt.mpr high), Bytes.toList_ofList]
  simp

private theorem negative_is_high (key : Int64) (negative : key.toInt < 0) :
    2 ^ 56 ≤ key.toUInt64.toNat := by
  rw [← Int64.toInt_toBitVec, BitVec.toInt_eq_toNat_cond, Int64.toNat_toBitVec] at negative
  split at negative <;> omega

theorem amount_roundtrip_nine (key amount : Int64) (high : 2 ^ 56 ≤ key.toUInt64.toNat) :
    let cell : BTree.LeafWrite.Cell := ⟨key, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    TableLeaf.cell? view 0 = some ⟨key, Bytes.ofList (Record.Write.amount amount), 0, 21⟩ ∧
    (TableLeaf.cell? view 0).bind TableLeaf.row? =
      some (key.toInt, [.integer key, .integer amount]) := by
  let digits := (Varint.encode key.toUInt64).toList
  have width : digits.length = 9 := key_width_nine key.toUInt64 high
  have parsed := Varint.read?_encode_nine _ 1 key.toUInt64 high fun i inside =>
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
  simpa [show (Varint.encode key.toUInt64).toList.length = 9 from width] using row


theorem amount_roundtrip_negative (key amount : Int64) (negative : key.toInt < 0) :
    let cell : BTree.LeafWrite.Cell := ⟨key, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    TableLeaf.cell? view 0 = some ⟨key, Bytes.ofList (Record.Write.amount amount), 0, 21⟩ ∧
    (TableLeaf.cell? view 0).bind TableLeaf.row? =
      some (key.toInt, [.integer key, .integer amount]) :=
  amount_roundtrip_nine key amount (negative_is_high key negative)

end Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.NineByte
