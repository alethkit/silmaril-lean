module

import Mathlib.Data.Fin.VecNotation
public import Silmaril.Logic.Arithmetic.Buchi.Thms

namespace Silmaril.Logic.Arithmetic.Buchi

open Silmaril.Inst Silmaril.Logic.Institution.Examples

example : valuation 0 = 0 := valuation_zero
example : valuation 7 = 1 := by decide +kernel
example : valuation 8 = 8 := by decide +kernel
example : valuation 12 = 4 := by decide +kernel

private def numeral : ℕ → UFOL.Term buchiSignature 0
  | 0 => .app (.additive .zero) Fin.elim0
  | n + 1 => .app (.additive .add) ![numeral n, .app (.additive .one) Fin.elim0]

/-- The closed sentence `V₂(12) = 4` holds in the Büchi institution. -/
example : buchi.Valid (S := ()) (.eq (.app .valuation ![numeral 12]) (numeral 4)) := by
  intro _
  change valuation 12 = 4
  decide +kernel

/-- The closed sentence `∀ x, x + 0 = x` survives the Presburger inclusion. -/
private def addZero : presburger.Sen () :=
  .all (.eq (.app .add ![.var 0, .app .zero Fin.elim0]) (.var 0))

example : buchi.Valid (S := ()) ((presburgerToBuchi.ρ.app ()).sen addZero) := by
  intro _
  exact ((presburgerToBuchi.ρ.app ()).sat () addZero).mpr (fun x => Nat.add_zero x)

end Silmaril.Logic.Arithmetic.Buchi
