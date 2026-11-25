module

public import Silmaril.Formats.Sqlite.Record.Write.Defs
public import Silmaril.Formats.Sqlite.Record.Defs
import Silmaril.Formats.Sqlite.File.Thms

public section
namespace Silmaril.Proofs.Formats.Sqlite.Record.Write

open Silmaril.Formats Silmaril.Formats.Sqlite

private theorem signed64 (value : Int64) :
    Int64.ofInt (File.signed 8 value.toUInt64.toNat) = value := by
  have same : File.signed 8 value.toUInt64.toNat = value.toInt := by
    rw [← Int64.toNat_toBitVec, ← Int64.toInt_toBitVec, BitVec.toInt_eq_toNat_cond]
    unfold File.signed
    split <;> split <;> omega
  rw [same, Int64.ofInt_toInt]

private theorem be64 (n : Nat) (bound : n < 256 ^ 8) :
    (File.Write.be 8 n).foldl (fun total byte => total * 256 + byte.toNat) 0 = n := by
  change ([0, 1, 2, 3, 4, 5, 6, 7].map (fun i : Nat =>
    UInt8.ofNat (n / 256 ^ (8 - 1 - i)))).foldl (fun total byte => total * 256 + byte.toNat) 0 = n
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, UInt8.toNat_ofNat',
    Nat.reduceSub, Nat.reducePow, Nat.zero_mul, Nat.zero_add, Nat.div_one]
  omega

private theorem getOfList (list : List UInt8) (i : Nat) (inside : i < list.length) :
    (File.View.ofBytes (Bytes.ofList list)).get? i = some list[i] := by
  have fits : i < (Bytes.ofList list).length := by simpa using inside
  simp only [File.View.get?, File.View.ofBytes, fits, ↓reduceIte, Nat.zero_add]
  have bounded : i < (Bytes.ofList list).data.size := fits
  simp only [getElem?_pos, bounded]
  exact congrArg some List.getElem_toByteArray

private theorem decodeFixed (encoding : File.TextEncoding) (a b c d e f g h : UInt8) :
    Record.decode? encoding (Bytes.ofList [3, 0, 6, a, b, c, d, e, f, g, h]) =
      some #[.null, .integer (Int64.ofInt (File.signed 8
        ([a, b, c, d, e, f, g, h].foldl (fun total byte => total * 256 + byte.toNat) 0)))] := by
  let list : List UInt8 := [3, 0, 6, a, b, c, d, e, f, g, h]
  let bytes := Bytes.ofList list
  let view := File.View.ofBytes bytes
  let nullView : File.View := ⟨bytes, 3, 0, by simp [bytes, list]⟩
  let intView : File.View := ⟨bytes, 3, 8, by simp [bytes, list]⟩
  have length : view.length = 11 := by simp [view, File.View.ofBytes, bytes, list]
  have get (i : Nat) (inside : i < 11) : view.get? i = some (list[i]'(by simpa [list] using inside)) :=
    getOfList list i (by simpa [list] using inside)
  have read0 : Varint.readNat? view 0 = some (3, 1) := by
    have first : view.get? 0 = some 3 := get 0 (by decide)
    simp [Varint.readNat?, Varint.readAux?, first]
  have read1 : Varint.readNat? view 1 = some (0, 2) := by
    have first : view.get? 1 = some 0 := get 1 (by decide)
    simp [Varint.readNat?, Varint.readAux?, first]
  have read2 : Varint.readNat? view 2 = some (6, 3) := by
    have first : view.get? 2 = some 6 := get 2 (by decide)
    simp [Varint.readNat?, Varint.readAux?, first]
  have sub0 : view.sub? 3 0 = some nullView := by simp [view, File.View.ofBytes, File.View.sub?, nullView, bytes, list]
  have sub8 : view.sub? 3 8 = some intView := by simp [view, File.View.ofBytes, File.View.sub?, intView, bytes, list]
  have parsed : Record.parse? view = some ⟨view, 3, #[⟨0, nullView⟩, ⟨6, intView⟩]⟩ := by
    simp [Record.parse?, Record.headerAux?, Record.columnsAux?, Record.serialType,
      Record.SerialType.width, length, read0, read1, read2, sub0, sub8]
  have getInt (i : Nat) (inside : i < 8) :
      intView.get? i = some (([a, b, c, d, e, f, g, h] : List UInt8)[i]) := by
    rw [File.View.sub?_read view intView 3 8 i sub8 inside, Nat.add_comm 3 i, get _ (by omega)]
    rfl
  have readInt : intView.be? 0 8 =
      some ([a, b, c, d, e, f, g, h].foldl (fun total byte => total * 256 + byte.toNat) 0) := by
    change ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).foldlM (fun acc i =>
      (intView.get? i).map (fun byte => acc * 256 + byte.toNat)) 0 = _
    simp [List.foldlM_cons, getInt, List.foldl_cons]
  change (Record.parse? view).bind (Record.Parsed.values? encoding) = _
  rw [parsed]
  simp [Record.Parsed.values?, Record.Column.value?, Record.serialType, readInt]

theorem decode_amount (encoding : File.TextEncoding) (value : Int64) :
    Record.decode? encoding (Bytes.ofList (Record.Write.amount value)) =
      some #[.null, .integer value] := by
  let n := value.toUInt64.toNat
  have bound : n < 256 ^ 8 := UInt64.toNat_lt value.toUInt64
  have decode : Record.decode? encoding (Bytes.ofList (Record.Write.amount value)) =
      some #[.null, .integer (Int64.ofInt (File.signed 8
        ((File.Write.be 8 n).foldl (fun total byte => total * 256 + byte.toNat) 0)))] :=
    decodeFixed encoding _ _ _ _ _ _ _ _
  rw [decode, be64 n bound, signed64 value]

end Silmaril.Proofs.Formats.Sqlite.Record.Write
