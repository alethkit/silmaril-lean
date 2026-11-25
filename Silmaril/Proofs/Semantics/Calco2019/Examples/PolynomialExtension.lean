module

public import Silmaril.Semantics.Calco2019.Examples.PolynomialExtension.Defs

public section

universe u

namespace Silmaril.Calco2019.Proofs.PolynomialExtension

open CategoryTheory MvPolynomial
open Silmaril.Calco2019.PolynomialExtension

theorem extension (A : Type u) (R : CommRingCat.{u}) :
    bimodule.IsFreeExtension (indeterminates A R) (coefficients A R) := by
  intro S g h
  change (A ⟶ (forget CommRingCat).obj S) at g
  change ∃! k : carrier A R ⟶ S, (↾fun i => k.hom (X i)) = g ∧ coefficients A R ≫ k = h
  refine ⟨CommRingCat.ofHom (eval₂Hom h.hom g), ⟨?_, ?_⟩, ?_⟩
  · ext i
    exact eval₂Hom_X' h.hom g i
  · exact CommRingCat.hom_ext (RingHom.ext (eval₂Hom_C h.hom g))
  · intro k hk
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      exact (congrArg (fun f : R ⟶ S => f.hom r) hk.2).trans (eval₂Hom_C h.hom g r).symm
    · intro i
      exact (congrArg (fun f : A ⟶ (forget CommRingCat).obj S => f i) hk.1).trans
        (eval₂Hom_X' h.hom g i).symm

end Silmaril.Calco2019.Proofs.PolynomialExtension
