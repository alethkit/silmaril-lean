module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Associator.Thms
public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Structure.Thms
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Centrality

/-! # Central value arrows and the exact λiter premonoidal tensor -/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open scoped MonoidalCategory

variable {S : Sig.{u}}

/-- Every value arrow commutes with arbitrary computations in either tensor position. -/
theorem pure_isCentral {A B : SynCat S} {f : A ⟶ B} (hf : IsPureMor f) :
    @PremonoidalCategory.IsCentral _ _ (computationTensor S) _ _ f :=
  pure_isCentral_proof hf

instance computationPremonoidal (S : Sig.{u}) : PremonoidalCategory (SynCat S) where
  toMonoidalCategoryStruct := computationTensor S
  tensorHom_def _ _ := rfl
  whiskerLeft_id := tensorLeft_id
  whiskerLeft_comp := tensorLeft_comp
  id_whiskerRight X Y := tensorRight_id Y X
  comp_whiskerRight f g W := tensorRight_comp W f g
  associator_central A B C :=
    pure_isCentral (MonoidalCategoryStruct.associator (⟨A⟩ : ValueCat S) ⟨B⟩ ⟨C⟩).hom.property
  leftUnitor_central X :=
    pure_isCentral (MonoidalCategoryStruct.leftUnitor (⟨X⟩ : ValueCat S)).hom.property
  rightUnitor_central X :=
    pure_isCentral (MonoidalCategoryStruct.rightUnitor (⟨X⟩ : ValueCat S)).hom.property
  associator_naturality_left := tensorAssociator_naturality_left
  associator_naturality_middle := tensorAssociator_naturality_middle
  associator_naturality_right := tensorAssociator_naturality_right
  leftUnitor_naturality := tensorLeftUnitor_naturality
  rightUnitor_naturality := tensorRightUnitor_naturality
  pentagon := fun W X Y Z => by exact computationPentagon W X Y Z
  triangle := fun X Y => by exact computationTriangle X Y

instance computationSymmetric (S : Sig.{u}) :
    @SymmetricPremonoidalCategory (SynCat S) _ (computationPremonoidal S) where
  braiding := tensorSwap
  naturality_left := tensorSwap_naturality_left
  naturality_right := tensorSwap_naturality_right
  braiding_central X Y := pure_isCentral (valueSwap X Y).hom.property
  symmetry X Y := by
    change (tensorSwap X Y).hom ≫ (tensorSwap Y X).hom = 𝟙 _
    rw [← tensorSwap_inv X Y, Iso.hom_inv_id]
  hexagon_forward := fun X Y Z => by exact computationHexagonForward X Y Z
  hexagon_reverse := fun X Y Z => by exact computationHexagonReverse X Y Z

instance valueBraided (S : Sig.{u}) : BraidedCategory (ValueCat S) :=
  BraidedCategory.ofCartesianMonoidalCategory

instance valuesFreyd (S : Sig.{u}) :
    @FreydCategory (ValueCat S) (SynCat S) _ _ _ _ (computationPremonoidal S)
      (computationSymmetric S) (values S) where
  obj_bijective := ⟨fun ⟨x⟩ ⟨y⟩ h => congrArg (fun z => (⟨z⟩ : ValueCat S)) h,
    fun X => ⟨⟨X⟩, rfl⟩⟩
  unitIso := valuesUnitIso S
  tensorIso := valuesTensorIso
  tensor_naturality_left f Z := by
    change tensorRight Z.obj f.hom ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ Z).hom
    simpa only [Category.comp_id, Category.id_comp] using (tensorRight_value (R := Z) f)
  tensor_naturality_right X {_ _} f := by
    change tensorLeft X.obj f.hom ≫ 𝟙 _ = 𝟙 _ ≫ (X ◁ f).hom
    simpa only [Category.comp_id, Category.id_comp] using (tensorLeft_value (R := X) f)
  associativity X Y Z := by
    change (tensorAssociator X.obj Y.obj Z.obj).hom ≫ tensorLeft X.obj (𝟙 _) ≫ 𝟙 _ =
      tensorRight Z.obj (𝟙 _) ≫ 𝟙 _ ≫ (tensorAssociator X.obj Y.obj Z.obj).hom
    simp
  left_unitality X := by
    change tensorRight X.obj (𝟙 _) ≫ 𝟙 _ ≫ (tensorLeftUnitor X.obj).hom = (tensorLeftUnitor X.obj).hom
    simp
  right_unitality X := by
    change tensorLeft X.obj (𝟙 _) ≫ 𝟙 _ ≫ (tensorRightUnitor X.obj).hom = (tensorRightUnitor X.obj).hom
    simp
  map_central f := pure_isCentral f.property
  braiding X Y := by
    change 𝟙 _ ≫ (tensorSwap X.obj Y.obj).hom = (tensorSwap X.obj Y.obj).hom ≫ 𝟙 _
    simp

/-- The syntactic Freyd inclusion satisfies the repaired central-unit boundary. -/
instance valuesCentralUnit (S : Sig.{u}) : FreydCategory.CentralUnit (values S) :=
  FreydCategory.CentralUnit.of_unitIso_eqToIso _ rfl rfl

end Silmaril.Thesis.LambdaIter.Syn.SynCat
