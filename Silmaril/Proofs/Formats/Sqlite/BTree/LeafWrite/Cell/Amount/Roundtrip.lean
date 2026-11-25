module

public import Silmaril.Formats.Sqlite.BTree.LeafWrite.Defs
public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Formats.Sqlite.Record.Write.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.Amount

private theorem signed64 (value : Int64) :
    Int64.ofInt (File.signed 8 value.toUInt64.toNat) = value := by
  have same : File.signed 8 value.toUInt64.toNat = value.toInt := by
    rw [← Int64.toNat_toBitVec, ← Int64.toInt_toBitVec, BitVec.toInt_eq_toNat_cond]
    unfold File.signed
    split <;> split <;> omega
  rw [same, Int64.ofInt_toInt]

private theorem getOfList (list : List UInt8) (i : Nat) (inside : i < list.length) :
    (File.View.ofBytes (Bytes.ofList list)).get? i = some list[i] := by
  have fits : i < (Bytes.ofList list).length := by simpa using inside
  simp only [File.View.get?, File.View.ofBytes, fits, ↓reduceIte, Nat.zero_add]
  have bounded : i < (Bytes.ofList list).data.size := fits
  simp only [getElem?_pos, bounded]
  exact congrArg some List.getElem_toByteArray

private theorem writer_bytes (key : Int64) (amount : Int64) :
    (BTree.LeafWrite.Cell.bytes ⟨key, Record.Write.amount amount⟩) =
      (11 :: (Varint.encode key.toUInt64).toList) ++ Record.Write.amount amount := by
  have sizeByte : (Varint.encode (UInt64.ofNat 11)).toList = [11] := rfl
  simp only [BTree.LeafWrite.Cell.bytes, Record.Write.amount_length, sizeByte,
    List.length_append, List.length_cons, List.length_nil]
  have noPad : 4 - (0 + 1 + (Varint.encode key.toUInt64).toList.length + 11) = 0 := by omega
  rw [noPad, List.replicate_zero, List.append_nil]
  rfl

/-- Read the actual complete serialized amount cell given the successful round-trip
of its encoded key. The remainder of the parser is independent of varint width. -/
theorem amount_roundtrip_of_key (key amount : Int64) :
    let cell : BTree.LeafWrite.Cell := ⟨key, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    let payloadAt := 1 + (Varint.encode key.toUInt64).toList.length
    Varint.read? view 1 = some (key.toUInt64, payloadAt) →
    TableLeaf.cell? view 0 =
      some ⟨key, Bytes.ofList (Record.Write.amount amount), 0, payloadAt + 11⟩ ∧
    (TableLeaf.cell? view 0).bind TableLeaf.row? =
      some (key.toInt, [.integer key, .integer amount]) := by
  dsimp only
  rw [writer_bytes]
  let leading := 11 :: (Varint.encode key.toUInt64).toList
  let data := Record.Write.amount amount
  let source := Bytes.ofList (leading ++ data)
  let view := File.View.ofBytes source
  let start := 1 + (Varint.encode key.toUInt64).toList.length
  change Varint.read? view 1 = some (key.toUInt64, start) → _
  intro keyRead
  have leadingLength : leading.length = start := by simp [leading, start, Nat.add_comm]
  have sourceLength : source.length = start + 11 := by simp [source, data, leadingLength]
  have sizeByte : view.get? 0 = some 11 :=
    getOfList (leading ++ data) 0 (by simp [leading])
  have sizeRead : Varint.readNat? view 0 = some (11, 1) := by
    simp [Varint.readNat?, Varint.readAux?, sizeByte]
  let payload : File.View := ⟨source, start, 11, by omega⟩
  have sub : view.sub? start 11 = some payload := by
    simp [view, File.View.sub?, File.View.ofBytes, sourceLength, payload]
  have extracted : payload.materialize = Bytes.ofList data := by
    change Bytes.mk ((leading ++ data).toByteArray.extract start (start + 11)) = _
    rw [List.toByteArray_append]
    apply congrArg Bytes.mk
    apply ByteArray.extract_append_eq_right
    · simpa using leadingLength.symm
    · simp [leadingLength, data]
  have available : start + 11 ≤ view.length := by
    change start + 11 ≤ source.length
    omega
  have cellRead : TableLeaf.cell? view 0 = some ⟨key, Bytes.ofList data, 0, start + 11⟩ := by
    simp [TableLeaf.cell?, sizeRead, keyRead, sub, extracted, signed64, available, guard]
  refine ⟨cellRead, ?_⟩
  change (TableLeaf.cell? view 0).bind TableLeaf.row? = _
  rw [cellRead]
  simp [TableLeaf.row?, data, Record.Write.decode_amount]

/-- The cell starts with the fixed payload length followed by the complete key encoding. -/
theorem encoded_key_byte (key amount : Int64) (i : Nat)
    (inside : i < (Varint.encode key.toUInt64).toList.length) :
    let cell : BTree.LeafWrite.Cell := ⟨key, Record.Write.amount amount⟩
    let view := File.View.ofBytes (Bytes.ofList cell.bytes)
    view.get? (1 + i) = (Varint.encode key.toUInt64).toList[i]? := by
  dsimp only
  rw [writer_bytes]
  let digits := (Varint.encode key.toUInt64).toList
  let bytes := (11 :: digits) ++ Record.Write.amount amount
  have bound : i < digits.length := inside
  have full : 1 + i < bytes.length := by
    simp [bytes]
    omega
  change (File.View.ofBytes (Bytes.ofList bytes)).get? (1 + i) = digits[i]?
  rw [getOfList bytes (1 + i) full, getElem?_pos digits i bound]
  simp [bytes, List.getElem_append_left bound, Nat.add_comm 1 i]

end Silmaril.Proofs.Formats.Sqlite.BTree.LeafWrite.Cell.Amount
