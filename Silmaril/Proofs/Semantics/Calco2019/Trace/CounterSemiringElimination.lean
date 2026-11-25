module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Elimination.Defs
import Mathlib.Tactic.Ring

public section

namespace Silmaril.Calco2019.Proofs.CounterSemiring

open Silmaril.Calco2019.CounterSemiring
open Scalar

private theorem coefficients : ∀ a b c d : Scalar,
    let x := star a
    let y := star d
    let p := star (a + b * y * c)
    let q := star (d + c * x * b)
    x + x * b * q * c * x = p ∧
      x * b * q = p * b * y ∧
      q * c * x = y * c * p ∧
      q = y + y * c * p * b * y := by decide

theorem eliminate_pair (direct intoFirst intoSecond fromFirst fromSecond a b c d : Scalar) :
    eliminate (eliminate direct intoFirst a fromFirst)
        (eliminate intoSecond intoFirst a b) (eliminate d c a b)
        (eliminate fromSecond c a fromFirst) =
      eliminate (eliminate direct intoSecond d fromSecond)
        (eliminate intoFirst intoSecond d c) (eliminate a b d c)
        (eliminate fromFirst b d fromSecond) := by
  let x := star a
  let y := star d
  let p := star (a + b * y * c)
  let q := star (d + c * x * b)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := coefficients a b c d
  change x + x * b * q * c * x = p at h₁
  change x * b * q = p * b * y at h₂
  change q * c * x = y * c * p at h₃
  change q = y + y * c * p * b * y at h₄
  change (direct + intoFirst * x * fromFirst) +
      (intoSecond + intoFirst * x * b) * q * (fromSecond + c * x * fromFirst) =
    (direct + intoSecond * y * fromSecond) +
      (intoFirst + intoSecond * y * c) * p * (fromFirst + b * y * fromSecond)
  calc
    _ = direct + intoFirst * (x + x * b * q * c * x) * fromFirst +
          intoFirst * (x * b * q) * fromSecond +
          intoSecond * (q * c * x) * fromFirst + intoSecond * q * fromSecond := by ring
    _ = direct + intoFirst * p * fromFirst + intoFirst * (p * b * y) * fromSecond +
          intoSecond * (y * c * p) * fromFirst + intoSecond * (y + y * c * p * b * y) * fromSecond := by
        rw [h₁, h₂, h₃, h₄]
    _ = _ := by ring

end Silmaril.Calco2019.Proofs.CounterSemiring
