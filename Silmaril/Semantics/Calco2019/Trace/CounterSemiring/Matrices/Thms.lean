module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Matrices.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.CounterSemiringMatrices

/-! # The co-Cartesian structure of finite weighted matrices -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.CounterSemiring.FiniteMatrix

open CategoryTheory CategoryTheory.Limits

theorem comp_apply {X Y Z : Object} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X.carrier) (z : Z.carrier) : (f ≫ g) x z = ∑ y, f x y * g y z := rfl

@[simp] theorem id_apply (X : Object) (x y : X.carrier) :
    (𝟙 X : X ⟶ X) x y = if x = y then 1 else 0 := rfl

@[simp] theorem relabel_comp {X Y Z : Object} (p : X.carrier → Y.carrier) (f : Y ⟶ Z)
    (x : X.carrier) (z : Z.carrier) : (relabel p ≫ f) x z = f (p x) z :=
  Proofs.CounterSemiringMatrices.relabel_comp p f x z

theorem comp_relabel {X Y Z : Object} (f : X ⟶ Y) (p : Y.carrier → Z.carrier)
    (x : X.carrier) (z : Z.carrier) :
    (f ≫ relabel p) x z = ∑ y, if p y = z then f x y else 0 :=
  Proofs.CounterSemiringMatrices.comp_relabel f p x z

theorem sum_has_colimit (X Y : Object) :
    Nonempty (IsColimit (BinaryCofan.mk (P := sum X Y) (relabel (X := X) Sum.inl)
      (relabel (X := Y) Sum.inr))) :=
  Proofs.CounterSemiringMatrices.sumColimit X Y

/-- Disjoint union of indices exhibits a categorical coproduct. -/
noncomputable def coproducts : Coproducts Object.{u} where
  sum := sum
  inl := relabel Sum.inl
  inr := relabel Sum.inr
  isColimit X Y := Classical.choice (sum_has_colimit X Y)

@[simp] theorem desc_inl_apply {X Y Z : Object} (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : X.carrier) (z : Z.carrier) : coproducts.desc f g (.inl x) z = f x z :=
  (relabel_comp (X := X) (Y := sum X Y) Sum.inl (coproducts.desc f g) x z).symm.trans
    (congrArg (fun h : X ⟶ Z => h x z) (coproducts.inl_desc f g))

@[simp] theorem desc_inr_apply {X Y Z : Object} (f : X ⟶ Z) (g : Y ⟶ Z)
    (y : Y.carrier) (z : Z.carrier) : coproducts.desc f g (.inr y) z = g y z :=
  (relabel_comp (X := Y) (Y := sum X Y) Sum.inr (coproducts.desc f g) y z).symm.trans
    (congrArg (fun h : Y ⟶ Z => h y z) (coproducts.inr_desc f g))

/-- The unique matrix with an empty family of rows. -/
def emptyInitial : IsInitial (⟨PEmpty.{u + 1}⟩ : Object.{u}) :=
  IsInitial.ofUniqueHom (fun _ => Matrix.of fun i _ => i.elim)
    (fun _ _ => Matrix.ext fun i _ => i.elim)

instance : HasInitial Object.{u} := emptyInitial.hasInitial

theorem isEmpty_of_initial {I : Object} (initial : IsInitial I) : IsEmpty I.carrier :=
  Proofs.CounterSemiringMatrices.isEmpty_of_initial initial

end Silmaril.Calco2019.CounterSemiring.FiniteMatrix
