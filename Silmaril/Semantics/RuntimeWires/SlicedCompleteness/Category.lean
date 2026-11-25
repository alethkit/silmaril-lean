module

public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms
public import Mathlib.CategoryTheory.Monoidal.Transport
import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Algebra
import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Interpretation

@[expose] public section

namespace Silmaril.RuntimeWires.Sliced

open CategoryTheory
open scoped MonoidalCategory

universe u v

variable {O : Type u}

/-- The category of ordered frontiers and seam classes of sheets. -/
structure Presented (S : Signature.{u,v} O) where
  word : List O

namespace Presented

variable {S : Signature.{u,v} O}

instance : Category (Presented S) where
  Hom X Y := SeamHom S X.word Y.word
  id X := SeamHom.id X.word
  comp f g := f.comp g
  id_comp f := by
    refine Quotient.inductionOn f (fun p => ?_)
    rfl
  comp_id f := by
    refine Quotient.inductionOn f (fun p => ?_)
    exact congrArg SeamHom.ofSheet (Proofs.SlicedCompleteness.then_empty p)
  assoc f g h := by
    refine Quotient.inductionOn₃ f g h (fun p q r => ?_)
    exact congrArg SeamHom.ofSheet (Proofs.SlicedCompleteness.then_assoc p q r)

variable (S)

/-- Interpret the seam category in the existing term presentation. -/
def toTerms : Presented S ⥤ Diagram.Presented S (noEquations S) where
  obj X := ⟨X.word⟩
  map f := f.toTermHom
  map_id _ := rfl
  map_comp f g := SeamHom.toTermHom_comp f g

instance : (toTerms S).Full where
  map_surjective f := ⟨SeamHom.fromTermHom f, SeamHom.termEquiv.apply_symm_apply f⟩

instance : (toTerms S).Faithful where
  map_injective h := SeamHom.termEquiv.injective h

instance : (toTerms S).EssSurj where
  mem_essImage X := ⟨⟨X.word⟩, ⟨Iso.refl X⟩⟩

instance : (toTerms S).IsEquivalence where

theorem toTerms_generator (e : S.Edge) :
    (toTerms S).map (SeamHom.ofSheet (Sheet.generator e) :
        (⟨S.source e⟩ : Presented S) ⟶ ⟨S.target e⟩) =
      Diagram.Presented.ofTerm (.gen e) :=
  Proofs.SlicedCompleteness.denote_encode (noEquations S) (.gen e)

variable {S}

/-- Tensor the lists and use the independent scheduling operation on seam classes. -/
instance tensorData : MonoidalCategoryStruct (Presented S) where
  tensorObj X Y := ⟨X.word ++ Y.word⟩
  whiskerLeft X {_ _} f := (SeamHom.id X.word).tensor f
  whiskerRight f X := f.tensor (SeamHom.id X.word)
  tensorHom f g := f.tensor g
  tensorUnit := ⟨[]⟩
  associator X Y Z := eqToIso (congrArg Presented.mk (List.append_assoc X.word Y.word Z.word))
  leftUnitor X := eqToIso (congrArg Presented.mk (List.nil_append X.word))
  rightUnitor X := eqToIso (congrArg Presented.mk (List.append_nil X.word))

variable (S)

private theorem identity_sandwich {C : Type*} [Category* C] {X Y : C} (f : X ⟶ Y) :
    f = 𝟙 X ≫ f ≫ 𝟙 Y :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

private theorem tensor_refl {C : Type*} [Category* C] [MonoidalCategory C] (X Y : C) :
    Iso.refl X ⊗ᵢ Iso.refl Y = Iso.refl (X ⊗ Y) := by
  apply Iso.ext
  exact MonoidalCategory.id_tensorHom_id X Y

private theorem associator_with_identities {C : Type*} [Category* C] [MonoidalCategory C]
    (X Y Z : C) :
    (((Iso.refl ((X ⊗ Y) ⊗ Z)).symm ≪≫ ((Iso.refl (X ⊗ Y)).symm ⊗ᵢ Iso.refl Z)) ≪≫
      α_ X Y Z ≪≫ ((Iso.refl X ⊗ᵢ Iso.refl (Y ⊗ Z)) ≪≫ Iso.refl (X ⊗ (Y ⊗ Z)))).hom =
        (α_ X Y Z).hom := by simp [tensor_refl]

private theorem leftUnitor_with_identities {C : Type*} [Category* C] [MonoidalCategory C] (X : C) :
    (((Iso.refl ((𝟙_ C) ⊗ X)).symm ≪≫ ((Iso.refl (𝟙_ C)).symm ⊗ᵢ Iso.refl X)) ≪≫
      λ_ X).hom = (λ_ X).hom := by simp [tensor_refl]

private theorem rightUnitor_with_identities {C : Type*} [Category* C] [MonoidalCategory C] (X : C) :
    (((Iso.refl (X ⊗ (𝟙_ C))).symm ≪≫ (Iso.refl X ⊗ᵢ (Iso.refl (𝟙_ C)).symm)) ≪≫
      ρ_ X).hom = (ρ_ X).hom := by simp [tensor_refl]

def inducingData : Monoidal.InducingFunctorData (toTerms S) where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  whiskerLeft_eq X {_ _} f := by
    exact (SeamHom.toTermHom_tensor (SeamHom.id X.word) f).trans
      (identity_sandwich ((toTerms S).obj X ◁ (toTerms S).map f))
  whiskerRight_eq {_ _} f X := by
    exact (SeamHom.toTermHom_tensor f (SeamHom.id X.word)).trans
      (identity_sandwich ((toTerms S).map f ▷ (toTerms S).obj X))
  tensorHom_eq f g := by
    exact (SeamHom.toTermHom_tensor f g).trans
      (identity_sandwich ((toTerms S).map f ⊗ₘ (toTerms S).map g))
  associator_eq X Y Z := by
    exact (eqToHom_map (toTerms S) (congrArg Presented.mk (List.append_assoc X.word Y.word Z.word))).trans
      (associator_with_identities ((toTerms S).obj X) ((toTerms S).obj Y) ((toTerms S).obj Z)).symm
  leftUnitor_eq X := by
    exact (eqToHom_map (toTerms S) (congrArg Presented.mk (List.nil_append X.word))).trans
      (leftUnitor_with_identities ((toTerms S).obj X)).symm
  rightUnitor_eq X := by
    exact (eqToHom_map (toTerms S) (congrArg Presented.mk (List.append_nil X.word))).trans
      (rightUnitor_with_identities ((toTerms S).obj X)).symm

instance monoidal : MonoidalCategory (Presented S) :=
  Monoidal.induced (toTerms S) (inducingData S)

instance : (toTerms S).Monoidal :=
  Monoidal.fromInducedMonoidal (toTerms S) (inducingData S)

variable {S} {A B X Y : List O}

/-- Typed sheet transport is categorical transport in the seam quotient. -/
theorem ofSheet_reindex (p : Sheet S A B) (a : A = X) (b : B = Y) :
    (SeamHom.ofSheet (p.reindex a b) : (⟨X⟩ : Presented S) ⟶ ⟨Y⟩) =
      eqToHom (congrArg (Presented.mk (S := S)) a.symm) ≫
        (SeamHom.ofSheet p : (⟨A⟩ : Presented S) ⟶ ⟨B⟩) ≫
        eqToHom (congrArg (Presented.mk (S := S)) b) := by
  cases a
  cases b
  simp [Sheet.reindex]

theorem whiskerLeft_ofSheet (W : List O) (p : Sheet S A B) :
    (⟨W⟩ : Presented S) ◁ (SeamHom.ofSheet p : (⟨A⟩ : Presented S) ⟶ ⟨B⟩) =
      SeamHom.ofSheet (p.padLeft W) := by rfl

theorem whiskerRight_ofSheet (W : List O) (p : Sheet S A B) :
    (SeamHom.ofSheet p : (⟨A⟩ : Presented S) ⟶ ⟨B⟩) ▷ (⟨W⟩ : Presented S) =
      SeamHom.ofSheet (p.padRight W) :=
  congrArg SeamHom.ofSheet (Proofs.SlicedCompleteness.then_empty (p.padRight W))

end Presented
end Silmaril.RuntimeWires.Sliced
