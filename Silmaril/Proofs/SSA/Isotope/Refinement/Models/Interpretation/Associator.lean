module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Structure

/-! # Interpretation of the native associator representatives -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation CategoryTheory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment} (K : ControlData M.toSeqData F)

private def routeRight {X Y Z : M.toSeqData.PureObject} (f : X ⟶ Y ⊗ Z) (A : M.toSeqData.PureObject) :
    X ⊗ A ⟶ Y ⊗ (Z ⊗ A) := f ▷ A ≫ (α_ Y Z A).hom

private def routeLeft {X Y Z : M.toSeqData.PureObject} (f : X ⟶ Y ⊗ Z) (A : M.toSeqData.PureObject) :
    X ⊗ A ⟶ (Y ⊗ A) ⊗ Z :=
  f ▷ A ≫ (α_ Y Z A).hom ≫ Y ◁ (CategoryTheory.BraidedCategory.braiding Z A).hom ≫ (α_ Y A Z).inv

/-- The actual native reassociation derivation denotes the chosen associator. -/
theorem denoteArrow_assocDeriv (A B C : τ) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.assocDeriv (F := F) A B C e) = M.associator A B C := by
  unfold Syntactic.assocDeriv
  rw [denoteArrow_unpack]
  let A' : M.toSeqData.PureObject := ⟨A⟩
  let B' : M.toSeqData.PureObject := ⟨B⟩
  let C' : M.toSeqData.PureObject := ⟨C⟩
  let I : M.toSeqData.PureObject := 𝟙_ M.toSeqData.PureObject
  let d : I ⟶ I := ⟨M.discard Silmaril.unit (by rw [TypeQuantity.unit_quantity]; exact le_top), M.toSeqData.discard_pure _ _⟩
  have hd : d = 𝟙 I := Subtype.ext (M.discard_unit _)
  let s₁ := routeLeft M (routeRight M (λ_ I).inv (A' ⊗ B')) C'
  let s₂ := routeRight M (routeLeft M (routeRight M (λ_ I).inv C') A') B'
  let s₃ := routeLeft M (routeRight M (λ_ I).inv C') B'
  let f := (λ_ ((A' ⊗ B') ⊗ C')).inv ≫ (α_ I (A' ⊗ B') C').inv ≫
    s₁ ≫ (I ⊗ C') ◁ (d ▷ (A' ⊗ B') ≫ (λ_ (A' ⊗ B')).hom) ≫ (α_ (I ⊗ C') A' B').inv ≫
    s₂ ≫ ((d ▷ A' ≫ (λ_ A').hom) ⊗ₘ (s₃ ≫ ((d ▷ B' ≫ (λ_ B').hom) ⊗ₘ (d ▷ C' ≫ (λ_ C').hom))))
  change f.val = _
  let g := (CategoryTheory.BraidedCategory.braiding (A' ⊗ B') C').hom ≫ (α_ C' A' B').inv ≫
    (CategoryTheory.BraidedCategory.braiding C' A').hom ▷ B' ≫ (α_ A' C' B').hom ≫ A' ◁ (CategoryTheory.BraidedCategory.braiding C' B').hom
  have hfg : f = g := by
    dsimp only [f, g, s₁, s₂, s₃, routeLeft, routeRight]
    rw [hd]
    simp only [I, MonoidalCategory.id_whiskerRight, Category.id_comp,
      BraidedCategory.braiding_tensor_left_hom, braiding_tensorUnit_left]
    monoidal
  have hg : g = (α_ A' B' C').hom := by
    dsimp only [g]
    simp only [BraidedCategory.braiding_tensor_left_hom, Category.assoc,
      Iso.hom_inv_id_assoc]
    rw [← MonoidalCategory.comp_whiskerRight_assoc, SymmetricCategory.symmetry]
    simp only [MonoidalCategory.id_whiskerRight, Category.id_comp, Iso.inv_hom_id_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp, SymmetricCategory.symmetry]
    simp
  exact congrArg Subtype.val (hfg.trans hg)

/-- The inverse native reassociation derivation denotes the chosen inverse associator. -/
theorem denoteArrow_assocInvDeriv (A B C : τ) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.assocInvDeriv (F := F) A B C e) = M.associatorInv A B C := by
  unfold Syntactic.assocInvDeriv
  rw [denoteArrow_unpack]
  let A' : M.toSeqData.PureObject := ⟨A⟩
  let B' : M.toSeqData.PureObject := ⟨B⟩
  let C' : M.toSeqData.PureObject := ⟨C⟩
  let I : M.toSeqData.PureObject := 𝟙_ M.toSeqData.PureObject
  let d : I ⟶ I := ⟨M.discard Silmaril.unit (by rw [TypeQuantity.unit_quantity]; exact le_top), M.toSeqData.discard_pure _ _⟩
  have hd : d = 𝟙 I := Subtype.ext (M.discard_unit _)
  let s₁ := routeRight M (routeLeft M (λ_ I).inv A') (B' ⊗ C')
  let s₂ := routeRight M (routeLeft M (routeLeft M (λ_ I).inv A') B') C'
  let s₃ := routeRight M (routeLeft M (λ_ I).inv A') B'
  let f := (λ_ (A' ⊗ (B' ⊗ C'))).inv ≫ (α_ I A' (B' ⊗ C')).inv ≫
    s₁ ≫ (I ⊗ A') ◁ (d ▷ (B' ⊗ C') ≫ (λ_ (B' ⊗ C')).hom) ≫ (α_ (I ⊗ A') B' C').inv ≫
    s₂ ≫ ((s₃ ≫ ((d ▷ A' ≫ (λ_ A').hom) ⊗ₘ (d ▷ B' ≫ (λ_ B').hom))) ⊗ₘ (d ▷ C' ≫ (λ_ C').hom))
  change f.val = _
  have h : f = (α_ A' B' C').inv := by
    dsimp only [f, s₁, s₂, s₃, routeLeft, routeRight]
    rw [hd]
    simp only [I, MonoidalCategory.id_whiskerRight, Category.id_comp, braiding_tensorUnit_left]
    monoidal
  exact congrArg Subtype.val h

end Silmaril.Isotope.Refinement.Models.Interpretation
