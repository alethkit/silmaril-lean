module

public import Silmaril.Semantics.Calco2019.FreeExtensions
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # The polynomial-ring example of CALCO §1.3 -/

@[expose] public section

noncomputable section

universe u

namespace Silmaril.Calco2019.PolynomialExtension

open CategoryTheory MvPolynomial

/-- A bimodule arrow assigns elements of a commutative ring to a set of variables. -/
def bimodule : Bimodule (Type u) CommRingCat.{u} :=
  (forget CommRingCat.{u}).toProfunctor

/-- The polynomial ring on the given variable set over the coefficient ring. -/
abbrev carrier (A : Type u) (R : CommRingCat.{u}) : CommRingCat.{u} :=
  CommRingCat.of (MvPolynomial A R)

/-- Each variable names its corresponding indeterminate. -/
def indeterminates (A : Type u) (R : CommRingCat.{u}) :
    bimodule.Hom A (carrier A R) :=
  ↾MvPolynomial.X

/-- Include the coefficient ring as constant polynomials. -/
def coefficients (A : Type u) (R : CommRingCat.{u}) : R ⟶ carrier A R :=
  CommRingCat.ofHom MvPolynomial.C

end Silmaril.Calco2019.PolynomialExtension
