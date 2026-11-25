module

public import Silmaril.Formats.Sqlite.Shell.Defs

public section

open Silmaril.Formats.Sqlite.Shell

namespace Silmaril.Proofs.Formats.Sqlite.Shell.Signed64

/-- Success preserves the exact mathematical integer parsed from the token. -/
theorem signed64_some_iff (text : String) (result : Int64) :
    signed64? text = some result ↔ text.toInt? = some result.toInt := by
  unfold signed64?
  cases parsed : text.toInt? with
  | none => simp
  | some value =>
    change (if -(2^63 : Int) ≤ value ∧ value < 2^63 then some (Int64.ofInt value) else none) =
      some result ↔ some value = some result.toInt
    by_cases bounds : -(2^63 : Int) ≤ value ∧ value < 2^63
    · rw [ite_eq_left bounds]
      simp only [Option.some.injEq]
      constructor
      · intro equal
        exact (Int64.toInt_ofInt_of_le bounds.1 bounds.2).symm.trans (congrArg Int64.toInt equal)
      · intro equal
        rw [equal, Int64.ofInt_toInt]
    · rw [ite_eq_right bounds]
      simp only [Option.some.injEq]
      constructor
      · intro impossible
        cases impossible
      · intro equal
        subst value
        exact (bounds ⟨result.le_toInt, result.toInt_lt⟩).elim

/-- Failure occurs on a rejected integer token or an integer outside Int64. -/
theorem signed64_none_iff (text : String) :
    signed64? text = none ↔ text.toInt? = none ∨
      ∃ value, text.toInt? = some value ∧ (value < -(2^63 : Int) ∨ 2^63 ≤ value) := by
  unfold signed64?
  cases parsed : text.toInt? with
  | none => simp
  | some value =>
    change (if -(2^63 : Int) ≤ value ∧ value < 2^63 then some (Int64.ofInt value) else none) =
      none ↔ some value = (none : Option Int) ∨
      ∃ parsedValue, some value = some parsedValue ∧ (parsedValue < -(2^63 : Int) ∨ 2^63 ≤ parsedValue)
    by_cases bounds : -(2^63 : Int) ≤ value ∧ value < 2^63
    · rw [ite_eq_left bounds]
      simp
      omega
    · rw [ite_eq_right bounds]
      simp
      omega

end Silmaril.Proofs.Formats.Sqlite.Shell.Signed64
