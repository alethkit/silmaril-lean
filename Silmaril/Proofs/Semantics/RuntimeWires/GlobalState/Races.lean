module

public import Silmaril.Semantics.RuntimeWires.GlobalState.Defs

public section

namespace Silmaril.RuntimeWires.Proofs

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory ComonObj

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {R X : C} [ComonObj X] (S : GlobalState R X)

private theorem discard_tensor {f : X ⟶ X} (hf : GlobalState.Discardable f) (g : X ⟶ X) :
    Δ[X] ≫ (f ⊗ₘ g) ≫ discardFirst X = g := by
  have h : (f ⊗ₘ g) ≫ (ε[X] ▷ X) = ε[X] ⊗ₘ g := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, hf, Category.comp_id]
  simp only [discardFirst, ← Category.assoc (f ⊗ₘ g), h, ComonObj.counit_comul_hom_assoc]
  simp

theorem race_last {f : X ⟶ X} (hf : GlobalState.Discardable f) (g : X ⟶ X) :
    S.race f g = S.update g := by
  unfold GlobalState.race GlobalState.update
  rw [reassoc_of% S.get_get, S.put_put,
    ← whiskerLeft_comp_assoc R (f ⊗ₘ g), ← whiskerLeft_comp_assoc R Δ[X], discard_tensor hf g]

private theorem put_whisker (g : X ⟶ X) :
    (S.put ▷ X) ≫ (R ◁ g) = ((R ⊗ X) ◁ g) ≫ (S.put ▷ X) :=
  (tensorHom_def S.put g).symm.trans (tensorHom_def' S.put g)

theorem update_comp (f g : X ⟶ X) :
    S.update f ≫ S.update g = S.update (f ≫ g) := by
  have h : Δ[X] ≫ (X ◁ g) ≫ discardFirst X = g := by
    rw [← id_tensorHom]
    exact discard_tensor (f := 𝟙 X) (Category.id_comp _) g
  unfold GlobalState.update
  simp only [Category.assoc]
  rw [← Category.assoc S.put, S.put_get]
  simp only [Category.assoc]
  rw [reassoc_of% (put_whisker S g), ← associator_inv_naturality_right_assoc, S.put_put,
    ← whiskerLeft_comp_assoc R (X ◁ g), ← whiskerLeft_comp_assoc R Δ[X], h,
    ← whiskerLeft_comp_assoc]

end Silmaril.RuntimeWires.Proofs
