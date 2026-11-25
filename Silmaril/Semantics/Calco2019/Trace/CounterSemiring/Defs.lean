module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Card

/-! # A five-element scalar witness for a missing Conway group identity

The four finite values are subsets of the cyclic group of order two.
The fifth value absorbs nonzero multiplication. Star distinguishes the
presence of the nonidentity group element.
-/

@[expose] public section

namespace Silmaril.Calco2019.CounterSemiring

inductive Scalar
  | empty
  | unit
  | generator
  | both
  | overflow
  deriving DecidableEq

namespace Scalar

instance : Fintype Scalar where
  elems := ⟨([.empty, .unit, .generator, .both, .overflow] : List Scalar), by decide⟩
  complete a := by cases a <;> decide

instance : Zero Scalar := ⟨.empty⟩
instance : One Scalar := ⟨.unit⟩

/-- Union of subsets, with an absorbing largest value. -/
instance : Add Scalar where
  add a b := match a, b with
    | .empty, b => b
    | a, .empty => a
    | .overflow, _ | _, .overflow => .overflow
    | .unit, .unit => .unit
    | .generator, .generator => .generator
    | _, _ => .both

/-- Setwise multiplication in the cyclic group of order two, with
`overflow` absorbing every nonempty factor. -/
instance : Mul Scalar where
  mul a b := match a, b with
    | .empty, _ | _, .empty => .empty
    | .overflow, _ | _, .overflow => .overflow
    | .unit, b => b
    | a, .unit => a
    | .generator, .generator => .unit
    | _, _ => .both

/-- Close the unit and the empty set to the unit. Values containing the
generator close to the largest scalar. -/
def star : Scalar → Scalar
  | .empty | .unit => .unit
  | _ => .overflow

end Scalar

end Silmaril.Calco2019.CounterSemiring
