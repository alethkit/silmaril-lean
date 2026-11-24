module

public import Silmaril.Logic.Arithmetic.Buchi.Defs

@[expose] public section

namespace Silmaril.Logic.Arithmetic.Buchi

@[simp] theorem valuation_zero : valuation 0 = 0 := rfl

/-- On a nonzero input, the valuation is a power of two whose exponent is maximal. -/
theorem valuation_greatest {n : ℕ} (hn : n ≠ 0) :
    ∃ k : ℕ, valuation n = 2 ^ k ∧ ∀ j : ℕ, 2 ^ j ∣ n ↔ j ≤ k := by
  refine ⟨padicValNat 2 n, ite_eq_right hn, fun j => ?_⟩
  rw [Nat.padicValNat_def]
  exact Nat.pow_dvd_iff_le_multiplicity (by decide) hn

/-- The unique standard additive model is the reduct of the standard Büchi model. -/
theorem presburgerToBuchi_modelExpansive : presburgerToBuchi.ModelExpansive :=
  fun _ ⟨⟩ => ⟨(), rfl⟩

end Silmaril.Logic.Arithmetic.Buchi
