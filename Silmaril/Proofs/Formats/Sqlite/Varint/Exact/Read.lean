module

public import Silmaril.Formats.Sqlite.Varint.Defs
import Silmaril.Formats.Sqlite.Varint.Normal.Thms
import Silmaril.Formats.Sqlite.Varint.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.Varint.Exact

private theorem ordinary_width_exists (value fuel : Nat) (positive : 0 < fuel)
    (fits : value < 128 ^ fuel) :
    ∃ width, 0 < width ∧ width ≤ fuel ∧
      (width = 1 ∨ 128 ^ (width - 1) ≤ value) ∧ value < 128 ^ width := by
  induction fuel with
  | zero => omega
  | succ fuel ih =>
    by_cases short : value < 128 ^ fuel
    · by_cases noFuel : fuel = 0
      · exact ⟨1, by decide, by omega, Or.inl rfl, by simpa [noFuel] using fits⟩
      · obtain ⟨width, positive, within, lower, upper⟩ := ih (by omega) short
        exact ⟨width, positive, by omega, lower, upper⟩
    · exact ⟨fuel + 1, by omega, Nat.le_refl _, Or.inr (by simpa using Nat.le_of_not_gt short), fits⟩

private theorem nine_width (value : UInt64) (high : 2 ^ 56 ≤ value.toNat) :
    (Varint.encode value).toList.length = 9 := by
  unfold Varint.encode
  rw [ite_eq_right (Nat.not_lt.mpr high), Bytes.toList_ofList]
  simp

/-- All UInt64 keys use either the ordinary decoder or its ninth-octet rule.
The exact encoded bytes suffice, at an arbitrary admitted view-relative offset. -/
theorem read_encode (view : File.View) (offset : Nat) (value : UInt64)
    (bytes : ∀ i, i < (Varint.encode value).toList.length →
      view.get? (offset + i) = (Varint.encode value).toList[i]?) :
    Varint.read? view offset = some (value, offset + (Varint.encode value).toList.length) := by
  by_cases ordinary : value.toNat < 2 ^ 56
  · obtain ⟨width, positive, within, lower, upper⟩ :=
      ordinary_width_exists value.toNat 8 (by decide) ordinary
    have length := Varint.encode_width_normal value width positive within lower upper
    rw [length]
    exact Varint.read?_encode_normal view offset value width positive within lower upper
      (fun i inside => bytes i (length.symm ▸ inside))
  · have high := Nat.le_of_not_gt ordinary
    have length := nine_width value high
    rw [length]
    exact Varint.read?_encode_nine view offset value high
      (fun i inside => bytes i (length.symm ▸ inside))

end Silmaril.Proofs.Formats.Sqlite.Varint.Exact
