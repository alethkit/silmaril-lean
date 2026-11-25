module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Matrices.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Finite copowers in the matrix countermodel -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.CounterSemiring.FiniteMatrix

open CategoryTheory CategoryTheory.Limits

/-- A copower of a matrix object repeats its index set in disjoint blocks. -/
noncomputable def copowerIndices (X : Object.{u}) (I : Type) [Finite I] : Object.{u} :=
  letI := Fintype.ofFinite I
  letI := Classical.decEq I
  ⟨I × X.carrier⟩

/-- The leg of each block is the matrix of the corresponding injection. -/
noncomputable def copowerCofan (X : Object.{u}) (I : Type) [Finite I] :
    Cofan (fun _ : I => X) :=
  Cofan.mk (copowerIndices X I) (fun i => relabel (fun x => (i, x)))

end Silmaril.Calco2019.CounterSemiring.FiniteMatrix
