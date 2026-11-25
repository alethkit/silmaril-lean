module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Matrices.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

public section

universe u

namespace Silmaril.Calco2019.Proofs.CounterSemiringMatrices

open CategoryTheory CategoryTheory.Limits
open Silmaril.Calco2019.CounterSemiring
open FiniteMatrix

theorem relabel_comp {X Y Z : Object} (p : X.carrier → Y.carrier) (f : Y ⟶ Z)
    (x : X.carrier) (z : Z.carrier) : (relabel p ≫ f) x z = f (p x) z := by
  change (∑ y : Y.carrier, (if p x = y then (1 : Scalar) else 0) * f y z) = f (p x) z
  simp [ite_mul]

theorem comp_relabel {X Y Z : Object} (f : X ⟶ Y) (p : Y.carrier → Z.carrier)
    (x : X.carrier) (z : Z.carrier) :
    (f ≫ relabel p) x z = ∑ y, if p y = z then f x y else 0 := by
  change (∑ y : Y.carrier, f x y * (if p y = z then (1 : Scalar) else 0)) = _
  simp only [mul_ite, mul_one, mul_zero]

theorem sumColimit (X Y : Object) :
    Nonempty (IsColimit (BinaryCofan.mk (P := sum X Y) (relabel (X := X) Sum.inl)
      (relabel (X := Y) Sum.inr))) := by
  refine ⟨BinaryCofan.isColimitMk (fun c => stack c.inl c.inr) ?_ ?_ ?_⟩
  · intro c
    exact Matrix.ext fun x z => relabel_comp (X := X) (Y := sum X Y) Sum.inl (stack c.inl c.inr) x z
  · intro c
    exact Matrix.ext fun y z => relabel_comp (X := Y) (Y := sum X Y) Sum.inr (stack c.inl c.inr) y z
  · intro c f hl hr
    refine Matrix.ext fun x z => ?_
    cases x with
    | inl x =>
      exact (relabel_comp (X := X) (Y := sum X Y) Sum.inl f x z).symm.trans
        (congrArg (fun m : X ⟶ c.pt => m x z) hl)
    | inr y =>
      exact (relabel_comp (X := Y) (Y := sum X Y) Sum.inr f y z).symm.trans
        (congrArg (fun m : Y ⟶ c.pt => m y z) hr)

theorem isEmpty_of_initial {I : Object.{u}} (initial : IsInitial I) : IsEmpty I.carrier := by
  refine ⟨fun i => ?_⟩
  let U : Object.{u} := ⟨PUnit.{u+1}⟩
  let f : I ⟶ U := Matrix.of fun _ _ => (0 : Scalar)
  let g : I ⟶ U := Matrix.of fun _ _ => (1 : Scalar)
  have e : (0 : Scalar) = 1 := congrArg (fun m : I ⟶ U => m i PUnit.unit) (initial.hom_ext f g)
  exact (by decide : (0 : Scalar) ≠ 1) e

end Silmaril.Calco2019.Proofs.CounterSemiringMatrices
