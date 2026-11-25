module

public import Silmaril.Formats.Sqlite.Varint.Defs

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.Varint.Normal

private theorem seven_length (width fuel value : Nat) (positive : 0 < width)
    (enough : width ≤ fuel) (lo : width = 1 ∨ 128 ^ (width - 1) ≤ value)
    (hi : value < 128 ^ width) : (Varint.seven fuel value).length = width := by
  induction width generalizing fuel value with
  | zero => omega
  | succ width ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases width with
      | zero =>
        have short : value < 128 := by simpa using hi
        simp [Varint.seven, short]
      | succ width =>
        have lower : 128 ^ (width + 1) ≤ value := by
          simpa using Or.resolve_left lo (by omega)
        have base : 128 ≤ 128 ^ (width + 1) := by
          rw [Nat.pow_succ]
          have pos := Nat.pow_pos (by decide : 0 < 128) (n := width)
          omega
        have cont : ¬value < 128 := by omega
        have quotientLo : 128 ^ width ≤ value / 128 :=
          (Nat.le_div_iff_mul_le (by decide)).mpr (by simpa [Nat.pow_succ] using lower)
        have quotientHi : value / 128 < 128 ^ (width + 1) :=
          (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa only [Nat.pow_succ] using hi)
        have tail := ih fuel (value / 128) (by omega) (by omega)
          (Or.inr (by simpa using quotientLo)) quotientHi
        simp [Varint.seven, cont, tail]

private theorem seven_value (fuel value : Nat) (positive : 0 < fuel)
    (hi : value < 128 ^ fuel) :
    (Varint.seven fuel value).foldl (fun acc digit => acc * 128 + digit.toNat % 128) 0 = value := by
  induction fuel generalizing value with
  | zero => omega
  | succ fuel ih =>
    by_cases small : value < 128
    · have byteValue : (UInt8.ofNat value).toNat = value := UInt8.toNat_ofNat_of_lt' (by
        change value < 256
        omega)
      simp [Varint.seven, small, byteValue, Nat.mod_eq_of_lt small]
    · have tailFits : value / 128 < 128 ^ fuel :=
        (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa only [Nat.pow_succ] using hi)
      have tailFuel : 0 < fuel := by
        by_contra hz
        have zero : fuel = 0 := by omega
        simp [zero] at hi
        omega
      have marked : (UInt8.ofNat (value % 128 + 128)).toNat = value % 128 + 128 := by
        apply UInt8.toNat_ofNat_of_lt'
        change _ < 256
        omega
      rw [Varint.seven, ite_eq_right small, List.foldl_append,
        ih (value / 128) tailFuel tailFits]
      simp only [List.foldl_cons, List.foldl_nil, marked]
      omega

/-- The ordinary encoder emits exactly the unique base-128 width below its
nine-octet cutoff, including the single-octet representation of zero. -/
theorem encode_width (value : UInt64) (width : Nat)
    (positive : 0 < width) (enough : width ≤ 8)
    (lo : width = 1 ∨ 128 ^ (width - 1) ≤ value.toNat)
    (hi : value.toNat < 128 ^ width) : (Varint.encode value).toList.length = width := by
  have bound : 128 ^ width ≤ 2 ^ 56 := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 128) enough
    exact h
  unfold Varint.encode
  rw [ite_eq_left (Nat.lt_of_lt_of_le hi bound), Bytes.toList_ofList]
  simp [seven_length width 8 value.toNat positive enough lo hi]

private def mark_continuations (digits : List UInt8) : List UInt8 :=
  (digits.zipIdx).map fun (digit, i) =>
    if i + 1 < digits.length then UInt8.ofNat (digit.toNat % 128 + 128)
    else UInt8.ofNat (digit.toNat % 128)

private theorem mark_singleton (digit : UInt8) :
    mark_continuations [digit] = [UInt8.ofNat (digit.toNat % 128)] := rfl

private theorem mark_cons_continuation (a b : UInt8) (tail : List UInt8) :
    mark_continuations (a :: b :: tail) = UInt8.ofNat (a.toNat % 128 + 128) :: mark_continuations (b :: tail) := by
  apply List.ext_getElem?
  intro i
  cases i with
  | zero => simp [mark_continuations]
  | succ i =>
    simp only [mark_continuations, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_cons_succ,
      Option.map_map]
    cases next : (b :: tail)[i]? with
    | none => rfl
    | some digit =>
      simp only [Option.map_some, Function.comp_apply, Nat.zero_add, List.length_cons]
      have same : i + 1 + 1 < tail.length + 1 + 1 ↔ i + 1 < tail.length + 1 := by omega
      simp [same]

private theorem readAux_marked (view : File.View) (digits : List UInt8)
    (fuel offset accum : Nat) (nonempty : 0 < digits.length) (enough : digits.length < fuel)
    (bytes : ∀ i, i < digits.length → view.get? (offset + i) = (mark_continuations digits)[i]?) :
    Varint.readAux? view fuel offset accum =
      some (digits.foldl (fun acc digit => acc * 128 + digit.toNat % 128) accum,
        offset + digits.length) := by
  induction digits generalizing fuel offset accum with
  | nil => simp at nonempty
  | cons a rest ih =>
    obtain ⟨remaining, rfl⟩ : ∃ remaining, fuel = remaining + 2 := by
      simp only [List.length_cons] at enough
      exact ⟨fuel - 2, by omega⟩
    cases rest with
    | nil =>
      have byte : view.get? offset = some (UInt8.ofNat (a.toNat % 128)) := by
        simpa [mark_singleton] using bytes 0 (by simp)
      have small : a.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
      have exactNat : (UInt8.ofNat (a.toNat % 128)).toNat = a.toNat % 128 := by
        apply UInt8.toNat_ofNat_of_lt'
        change _ < 256
        omega
      rw [Varint.readAux?, byte]
      simp [exactNat, small, Nat.mod_eq_of_lt small]
    | cons b tail =>
      have byte : view.get? offset = some (UInt8.ofNat (a.toNat % 128 + 128)) := by
        simpa [mark_cons_continuation] using bytes 0 (by simp)
      have exactNat : (UInt8.ofNat (a.toNat % 128 + 128)).toNat = a.toNat % 128 + 128 := by
        apply UInt8.toNat_ofNat_of_lt'
        change _ < 256
        omega
      have next (i : Nat) (inside : i < (b :: tail).length) :
          view.get? (offset + 1 + i) = (mark_continuations (b :: tail))[i]? := by
        have width : i + 1 < (a :: b :: tail).length := by
          simp only [List.length_cons] at inside ⊢
          omega
        have observation := bytes (i + 1) width
        simpa [mark_cons_continuation, Nat.add_assoc, Nat.add_comm 1 i] using observation
      rw [Varint.readAux?, byte]
      change (if (UInt8.ofNat (a.toNat % 128 + 128)).toNat < 128 then _ else _) = _
      rw [exactNat, ite_eq_right (by omega), Nat.add_mod_right, Nat.mod_mod]
      rw [ih (remaining + 1) (offset + 1) _ (by simp) (by
        simp only [List.length_cons] at enough ⊢
        omega) next]
      simp [Nat.add_assoc, Nat.add_comm 1]

theorem read_encode_normal (view : File.View) (offset : Nat) (value : UInt64) (width : Nat)
    (positive : 0 < width) (enough : width ≤ 8)
    (lo : width = 1 ∨ 128 ^ (width - 1) ≤ value.toNat)
    (hi : value.toNat < 128 ^ width)
    (bytes : ∀ i, i < width → view.get? (offset + i) = (Varint.encode value).toList[i]?) :
    Varint.read? view offset = some (value, offset + width) := by
  have fits : value.toNat < 128 ^ 8 :=
    Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) enough)
  let digits := Varint.seven 8 value.toNat
  have count : digits.length = width := seven_length width 8 value.toNat positive enough lo hi
  have encoding : (Varint.encode value).toList = mark_continuations digits := by
    unfold Varint.encode
    rw [ite_eq_left fits, Bytes.toList_ofList]
    rfl
  have observations (i : Nat) (inside : i < digits.length) :
      view.get? (offset + i) = (mark_continuations digits)[i]? := by
    rw [← encoding]
    exact bytes i (count ▸ inside)
  have decoded := readAux_marked view digits 9 offset 0 (by omega) (by omega) observations
  rw [Varint.read?, Varint.readNat?, decoded, count]
  have valueEq : digits.foldl (fun acc digit => acc * 128 + digit.toNat % 128) 0 = value.toNat :=
    seven_value 8 value.toNat (by decide) fits
  simp [valueEq]

end Silmaril.Proofs.Formats.Sqlite.Varint.Normal
