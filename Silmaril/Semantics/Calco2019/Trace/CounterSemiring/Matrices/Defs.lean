module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Thms
public import Silmaril.Semantics.Calco2019.Defs
public import Mathlib.Data.Matrix.Mul

/-! # Finite matrices over the Conway counterexample semiring -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.CounterSemiring.FiniteMatrix

open CategoryTheory

/-- The row and column index types of the weighted matrix category. -/
structure Object where
  carrier : Type u
  [finite : Fintype carrier]
  [decEq : DecidableEq carrier]

attribute [instance] Object.finite Object.decEq

instance : Category.{u} Object.{u} where
  Hom X Y := Matrix X.carrier Y.carrier Scalar
  id _ := 1
  comp f g := f * g
  id_comp := Matrix.one_mul
  comp_id := Matrix.mul_one
  assoc := Matrix.mul_assoc

/-- A function of indices acts by its matrix of zeroes and ones. -/
def relabel {X Y : Object} (p : X.carrier → Y.carrier) : X ⟶ Y :=
  Matrix.of (fun x y => if p x = y then 1 else 0)

/-- The coproduct index type, with the two blocks distinguished by their tags. -/
def sum (X Y : Object.{u}) : Object.{u} := ⟨X.carrier ⊕ Y.carrier⟩

/-- Stack matrices with the same output index type. -/
def stack {X Y Z : Object} (f : X ⟶ Z) (g : Y ⟶ Z) : sum X Y ⟶ Z :=
  Matrix.of (Sum.elim f g)

end Silmaril.Calco2019.CounterSemiring.FiniteMatrix
