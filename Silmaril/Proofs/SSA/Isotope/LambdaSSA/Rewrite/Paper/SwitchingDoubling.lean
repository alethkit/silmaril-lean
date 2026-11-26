module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Blocks.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

/-! # Native doubling for two repeat-only switching rows -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoubling

open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X Y B : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "S" => Obj (Silmaril.coprod X Y)

set_option backward.isDefEq.respectTransparency false

theorem iterate_double_of_switching_rows (g : S ⟶ Obj B ⨿ S)
    (left : Obj X ⟶ Obj Y) (right : Obj Y ⟶ Obj X)
    (hl : (sumCofan X Y).inl ≫ g = left ≫ (sumCofan X Y).inr ≫ coprod.inr)
    (hr : (sumCofan X Y).inr ≫ g = right ≫ (sumCofan X Y).inl ≫ coprod.inr) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g := by
  let i : Obj X ⟶ S := (sumCofan X Y).inl
  let j : Obj Y ⟶ S := (sumCofan X Y).inr
  let leftRow : Obj X ⟶ (Obj B ⨿ Obj X) ⨿ Obj Y := left ≫ coprod.inr
  let rightRow : Obj Y ⟶ (Obj B ⨿ Obj X) ⨿ Obj Y := right ≫ coprod.inr ≫ coprod.inl
  let leftLoop : Obj X ⟶ Obj B ⨿ Obj X := left ≫ right ≫ coprod.inr
  let rightLoop : Obj Y ⟶ Obj B ⨿ Obj Y := right ≫ left ≫ coprod.inr
  let doubled : S ⟶ Obj B ⨿ S := g ≫ coprod.desc coprod.inl g
  have joined : blockCopair leftRow rightRow ≫ joinBlockExits X Y (Obj B) = g := by
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit X Y)
    · change i ≫ (blockCopair leftRow rightRow ≫ joinBlockExits X Y (Obj B)) = i ≫ g
      rw [← Category.assoc i, show i ≫ blockCopair leftRow rightRow = leftRow from inl_blockCopair _ _,
        show i ≫ g = left ≫ j ≫ coprod.inr from hl]
      simp [leftRow, joinBlockExits, j, Category.assoc]
      rfl
    · change j ≫ (blockCopair leftRow rightRow ≫ joinBlockExits X Y (Obj B)) = j ≫ g
      rw [← Category.assoc j, show j ≫ blockCopair leftRow rightRow = rightRow from inr_blockCopair _ _,
        show j ≫ g = right ≫ i ≫ coprod.inr from hr]
      simp [rightRow, joinBlockExits, i, Category.assoc]
  have exitRight : iterate rightRow = right ≫ (coprod.inr : Obj X ⟶ Obj B ⨿ Obj X) := by
    calc
      _ = rightRow ≫ coprod.desc (𝟙 _) (iterate rightRow) := iterate_fixpoint rightRow
      _ = _ := by simp [rightRow, Category.assoc]
  have nested : leftRow ≫ coprod.desc (𝟙 (Obj B ⨿ Obj X)) (iterate rightRow) = leftLoop := by
    rw [exitRight]
    simp [leftRow, leftLoop, Category.assoc]
  have single : iterate g = blockCopair (iterate leftLoop) (right ≫ iterate leftLoop) := by
    have eq := iterate_join_blocks X Y (Obj B) leftRow rightRow
    dsimp only at eq
    rw [joined, nested, exitRight] at eq
    simpa only [Category.assoc, coprod.inr_desc] using eq
  have rotate : iterate rightLoop = right ≫ iterate leftLoop := by
    have eq := iterate_roll right (left ≫ (coprod.inr : Obj Y ⟶ Obj B ⨿ Obj Y))
    simpa only [rightLoop, leftLoop, Category.assoc, coprod.inr_map] using eq
  have leftDouble : leftLoop ≫ coprod.map (𝟙 (Obj B)) i = i ≫ doubled := by
    unfold doubled
    rw [← Category.assoc i g, show i ≫ g = left ≫ j ≫ coprod.inr from hl]
    simp only [leftLoop, Category.assoc, coprod.inr_map, coprod.inr_desc]
    rw [show j ≫ g = right ≫ i ≫ coprod.inr from hr]
  have rightDouble : rightLoop ≫ coprod.map (𝟙 (Obj B)) j = j ≫ doubled := by
    unfold doubled
    rw [← Category.assoc j g, show j ≫ g = right ≫ i ≫ coprod.inr from hr]
    simp only [rightLoop, Category.assoc, coprod.inr_map, coprod.inr_desc]
    rw [show i ≫ g = left ≫ j ≫ coprod.inr from hl]
  have ic : ConstructorReturn i := ⟨_, .inl (.var (i := 0) rfl), sumCofan_inl X Y⟩
  have jc : ConstructorReturn j := ⟨_, .inr (.var (i := 0) rfl), sumCofan_inr X Y⟩
  change iterate doubled = iterate g
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit X Y)
  · change i ≫ iterate doubled = i ≫ iterate g
    rw [← iterate_uniformity_ofConstructorReturn ic leftLoop doubled leftDouble, single]
    exact (inl_blockCopair _ _).symm
  · change j ≫ iterate doubled = j ≫ iterate g
    rw [← iterate_uniformity_ofConstructorReturn jc rightLoop doubled rightDouble, rotate, single]
    exact (inr_blockCopair _ _).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoubling
