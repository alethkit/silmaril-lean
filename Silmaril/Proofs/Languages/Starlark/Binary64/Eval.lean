module

public import Silmaril.Languages.Starlark.Binary64.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Binary64

open Silmaril.Languages.Starlark.Binary64

private theorem abs_magnitude (input : UInt64) : (abs input).toNat = input.toNat % 2 ^ 63 := by
  rw [abs, UInt64.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod input.toNat 63

theorem absolute_iff_abs (input output : UInt64) : Absolute input output ↔ abs input = output := by
  rw [Absolute, ← abs_magnitude input, UInt64.toNat_inj, eq_comm]

theorem truth_iff_truth (input : UInt64) (out : Bool) : Truth input out ↔ truth input = out := by
  have zero : abs input = 0 ↔ input.toNat % 2 ^ 63 = 0 := by
    rw [← UInt64.toNat_inj, abs_magnitude]
    rfl
  constructor
  · intro ran
    cases ran with
    | zero magnitude => simp [truth, zero.mpr magnitude]
    | nonzero magnitude => simp [truth, mt zero.mp magnitude]
  · intro result
    cases out with
    | false =>
      exact .zero (zero.mp (by simpa [truth] using result))
    | true =>
      exact .nonzero (mt zero.mpr (by simpa [truth] using result))

theorem truth_false_iff_signed_zero (input : UInt64) :
    truth input = false ↔ input = 0 ∨ input = 0x8000000000000000 := by
  rw [← truth_iff_truth]
  constructor
  · intro ran
    cases ran with
    | zero magnitude =>
      have bound : input.toNat < 0x10000000000000000 := input.toNat_lt_size
      change input.toNat % 0x8000000000000000 = 0 at magnitude
      have encoding : input.toNat = 0 ∨ input.toNat = 0x8000000000000000 := by omega
      exact encoding.imp UInt64.toNat_inj.mp UInt64.toNat_inj.mp
  · rintro (rfl | rfl) <;> exact .zero (by decide)

end Silmaril.Proofs.Languages.Starlark.Binary64
