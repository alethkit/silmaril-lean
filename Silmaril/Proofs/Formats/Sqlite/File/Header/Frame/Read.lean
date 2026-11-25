module

public import Silmaril.Formats.Sqlite.File.Defs

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.File.Header.Frame

private theorem all_frame {values : List Nat} {f g : Nat → Bool}
    (same : ∀ i, i ∈ values → f i = g i) : values.all f = values.all g := by
  induction values with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.all_cons, same i (by simp), ih (fun j hj => same j (by simp [hj]))]

private theorem fold_frame {values : List Nat} {f g : Nat → Nat → Option Nat}
    (acc : Nat) (same : ∀ i, i ∈ values → ∀ n, f n i = g n i) :
    values.foldlM f acc = values.foldlM g acc := by
  induction values generalizing acc with
  | nil => rfl
  | cons i rest ih =>
    have tail (n : Nat) := ih n fun j hj => same j (by simp [hj])
    simp only [List.foldlM_cons, same i (by simp), tail]

theorem parseHeader?_frame (left right : Bytes)
    (leftFits : 100 ≤ left.length) (rightFits : 100 ≤ right.length)
    (same : ∀ i, i < 100 → (File.View.ofBytes left).get? i = (File.View.ofBytes right).get? i) :
    File.parseHeader? left = File.parseHeader? right := by
  have field (offset width : Nat) (fits : offset + width ≤ 100) :
      (File.View.ofBytes left).be? offset width = (File.View.ofBytes right).be? offset width := by
    unfold File.View.be?
    apply fold_frame
    intro i member _
    have inside := List.mem_range.mp member
    rw [same (offset + i) (by omega)]
  have magic : (List.range 16).all (fun i => (File.View.ofBytes left).get? i == File.headerMagic[i]?) =
      (List.range 16).all (fun i => (File.View.ofBytes right).get? i == File.headerMagic[i]?) := by
    apply all_frame
    intro i member
    have inside := List.mem_range.mp member
    rw [same i (by omega)]
  have reserved : (List.range 20).all (fun i => (File.View.ofBytes left).get? (72+i) == some 0) =
      (List.range 20).all (fun i => (File.View.ofBytes right).get? (72+i) == some 0) := by
    apply all_frame
    intro i member
    have inside := List.mem_range.mp member
    rw [same (72+i) (by omega)]
  unfold File.parseHeader?
  simp only [ite_eq_right (Nat.not_lt.mpr leftFits), ite_eq_right (Nat.not_lt.mpr rightFits), magic, reserved,
    field 16 2 (by decide), field 18 1 (by decide), field 19 1 (by decide), field 20 1 (by decide),
    field 21 1 (by decide), field 22 1 (by decide), field 23 1 (by decide), field 44 4 (by decide),
    field 56 4 (by decide), field 52 4 (by decide), field 64 4 (by decide), field 24 4 (by decide),
    field 28 4 (by decide), field 32 4 (by decide), field 36 4 (by decide), field 40 4 (by decide),
    field 48 4 (by decide), field 60 4 (by decide), field 68 4 (by decide), field 92 4 (by decide),
    field 96 4 (by decide)]

theorem parse?_descriptor_frame (left right : Bytes)
    (length : left.length = right.length)
    (same : ∀ i, i < 100 → (File.View.ofBytes left).get? i = (File.View.ofBytes right).get? i) :
    (File.parse? left).map (fun image => (image.header, image.pageCount, image.physicalPageCount)) =
      (File.parse? right).map (fun image => (image.header, image.pageCount, image.physicalPageCount)) := by
  have headers : File.parseHeader? left = File.parseHeader? right := by
    by_cases fits : 100 ≤ left.length
    · exact parseHeader?_frame left right fits (length ▸ fits) same
    · have short : left.length < 100 := by omega
      have rightShort : right.length < 100 := by omega
      simp [File.parseHeader?, short, rightShort]
  unfold File.parse?
  rw [headers, length]
  cases decoded : File.parseHeader? right with
  | none => rfl
  | some header =>
    simp
    split
    · split <;> simp_all
      all_goals split <;> simp_all
    · simp_all

end Silmaril.Proofs.Formats.Sqlite.File.Header.Frame
