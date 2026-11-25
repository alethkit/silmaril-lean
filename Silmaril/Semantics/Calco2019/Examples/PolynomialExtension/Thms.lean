module

public import Silmaril.Semantics.Calco2019.Examples.PolynomialExtension.Defs
public import Silmaril.Semantics.Calco2019.Thms
import Silmaril.Proofs.Semantics.Calco2019.Examples.PolynomialExtension

/-! # The polynomial free extension and its coproduct characterization -/

public section

noncomputable section

universe u

namespace Silmaril.Calco2019.PolynomialExtension

open CategoryTheory CategoryTheory.Limits

/-- Polynomial rings are free extensions of commutative rings by their variable sets,
including the two-variable instance in §1.3. -/
def extension (A : Type u) (R : CommRingCat.{u}) : bimodule.FreeExtension A R where
  pt := carrier A R
  generator := indeterminates A R
  inclusion := coefficients A R
  isFreeExtension := Proofs.PolynomialExtension.extension A R

/-- Polynomials over the initial ring form the free commutative ring on the variable set. -/
def freeRing (A : Type u) : bimodule.FreeObject A where
  pt := carrier A (CommRingCat.of (ULift.{u} ℤ))
  generator := indeterminates A _
  isFreeObject := by
    let Z := CommRingCat.of (ULift.{u} ℤ)
    have eq : CommRingCat.isInitial.to (carrier A Z) = coefficients A Z :=
      CommRingCat.isInitial.hom_ext _ _
    exact (isFreeExtension_initial_iff CommRingCat.isInitial _).mp
      (eq.symm ▸ (extension A Z).isFreeExtension)

/-- The polynomial extension is the coproduct of the free ring on its
variables and the coefficient ring. -/
theorem coproduct (A : Type u) (R : CommRingCat.{u}) :
    ∃! l : (freeRing A).pt ⟶ carrier A R,
      bimodule.post (freeRing A).generator l = indeterminates A R ∧
        Nonempty (IsColimit (BinaryCofan.mk l (coefficients A R))) :=
  freeExtension_coprodLeg (freeRing A).isFreeObject (extension A R).isFreeExtension

end Silmaril.Calco2019.PolynomialExtension
