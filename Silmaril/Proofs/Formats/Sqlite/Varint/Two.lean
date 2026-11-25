module
public import Silmaril.Formats.Sqlite.Varint.Defs

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.Varint.Two

private theorem encode_list (value : UInt64) (lo : 128 ≤ value.toNat) (hi : value.toNat < 16384) :
    (Varint.encode value).toList =
      [UInt8.ofNat (value.toNat / 128 + 128), UInt8.ofNat (value.toNat % 128)] := by
  have highDigit : value.toNat / 128 < 128 := by omega
  have lowDigit : value.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
  have lowByte : value.toNat % 128 + 128 < 256 := by omega
  have small : value.toNat < 2 ^ 56 := by omega
  unfold Varint.encode
  rw [ite_eq_left small, Bytes.toList_ofList, Varint.seven, ite_eq_right (by omega),
    Varint.seven, ite_eq_left highDigit]
  change [UInt8.ofNat ((UInt8.ofNat (value.toNat / 128)).toNat % 128 + 128),
    UInt8.ofNat ((UInt8.ofNat (value.toNat % 128 + 128)).toNat % 128)] = _
  rw [UInt8.toNat_ofNat_of_lt' (by change _ < 256; omega), UInt8.toNat_ofNat_of_lt' lowByte,
    Nat.mod_eq_of_lt highDigit]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt lowDigit]

theorem read_encode (view : File.View) (offset : Nat) (value : UInt64)
    (lo : 128 ≤ value.toNat) (hi : value.toNat < 16384)
    (bytes : ∀ i, i < 2 → view.get? (offset + i) = (Varint.encode value).toList[i]?) :
    Varint.read? view offset = some (value, offset + 2) := by
  have highDigit : value.toNat / 128 < 128 := by omega
  have lowDigit : value.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
  have first : view.get? offset = some (UInt8.ofNat (value.toNat / 128 + 128)) := by
    simpa [encode_list value lo hi] using bytes 0 (by decide)
  have last : view.get? (offset + 1) = some (UInt8.ofNat (value.toNat % 128)) := by
    simpa [encode_list value lo hi] using bytes 1 (by decide)
  have firstNat : (UInt8.ofNat (value.toNat / 128 + 128)).toNat =
      value.toNat / 128 + 128 := UInt8.toNat_ofNat_of_lt' (by change _ < 256; omega)
  have lastNat : (UInt8.ofNat (value.toNat % 128)).toNat = value.toNat % 128 :=
    UInt8.toNat_ofNat_of_lt' (by change _ < 256; omega)
  unfold Varint.read? Varint.readNat?
  rw [Varint.readAux?, first]
  change Option.map _ (if (UInt8.ofNat (value.toNat / 128 + 128)).toNat < 128 then _ else _) = _
  rw [firstNat, ite_eq_right (by omega), Varint.readAux?, last]
  change Option.map _ (if (UInt8.ofNat (value.toNat % 128)).toNat < 128 then _ else _) = _
  rw [lastNat, ite_eq_left lowDigit]
  have combined : (0 * 128 + (value.toNat / 128 + 128) % 128) * 128 +
      value.toNat % 128 % 128 = value.toNat := by omega
  rw [combined]
  simp [UInt64.ofNat_toNat, Nat.add_assoc]

end Silmaril.Proofs.Formats.Sqlite.Varint.Two
