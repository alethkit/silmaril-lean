module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Blocks.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

/-! # Binary decomposition and finite block elimination in Paper -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BlockElimination

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => Paper.TypeCategory (τ := τ) Φ
local notation "iter" => Paper.TypeCategory.iterate

set_option backward.isDefEq.respectTransparency false

private theorem inl_constructor (A D : τ) : ConstructorReturn (sumCofan (Φ := Φ) A D).inl :=
  ⟨_, .inl (.var (i := 0) rfl), sumCofan_inl A D⟩

private theorem inr_constructor (A D : τ) : ConstructorReturn (sumCofan (Φ := Φ) A D).inr :=
  ⟨_, .inr (.var (i := 0) rfl), sumCofan_inr A D⟩

private theorem map_desc {A B C D T : Comp} (f : A ⟶ C) (g : B ⟶ D) (l : C ⟶ T) (r : D ⟶ T) :
    coprod.map f g ≫ coprod.desc l r = coprod.desc (f ≫ l) (g ≫ r) := by
  apply coprod.hom_ext <;> simp

@[reassoc (attr := simp)] theorem inl_blockCopair {A D : τ} {Y : Comp}
    (f : ofType A ⟶ Y) (g : ofType D ⟶ Y) : (sumCofan A D).inl ≫ blockCopair f g = f :=
  (sumCofanIsColimit A D).fac (BinaryCofan.mk f g) ⟨.left⟩

@[reassoc (attr := simp)] theorem inr_blockCopair {A D : τ} {Y : Comp}
    (f : ofType A ⟶ Y) (g : ofType D ⟶ Y) : (sumCofan A D).inr ≫ blockCopair f g = g :=
  (sumCofanIsColimit A D).fac (BinaryCofan.mk f g) ⟨.right⟩

theorem split_join (A D : τ) (Y : Comp) :
    splitBlockExits A D Y ≫ joinBlockExits A D Y = 𝟙 _ := by
  apply coprod.hom_ext
  · simp [splitBlockExits, joinBlockExits]
  · rw [Category.comp_id]
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit A D)
    · simp [splitBlockExits, joinBlockExits]
    · simp [splitBlockExits, joinBlockExits]
      rfl

theorem iterate_join_blocks (A D : τ) (Y : Comp)
    (f : ofType A ⟶ (Y ⨿ ofType A) ⨿ ofType D)
    (g : ofType D ⟶ (Y ⨿ ofType A) ⨿ ofType D) :
    let right := iter g
    let left := iter (f ≫ coprod.desc (𝟙 (Y ⨿ ofType A)) right)
    iter (blockCopair f g ≫ joinBlockExits A D Y) =
      blockCopair left (right ≫ coprod.desc (𝟙 Y) left) := by
  let S := ofType (Φ := Φ) (Silmaril.coprod A D)
  let i : ofType A ⟶ S := (sumCofan A D).inl
  let j : ofType D ⟶ S := (sumCofan A D).inr
  let passLeft : Y ⨿ ofType A ⟶ Y ⨿ S := coprod.map (𝟙 Y) i
  let sides : S ⟶ (Y ⨿ ofType A) ⨿ ofType D := blockCopair f g
  let inner : S ⟶ (Y ⨿ S) ⨿ S := sides ≫ coprod.map passLeft j
  let leftBody := f ≫ coprod.desc (𝟙 (Y ⨿ ofType A)) (iter g)
  have sideLeft : i ≫ sides = f := inl_blockCopair f g
  have sideRight : j ≫ sides = g := inr_blockCopair f g
  have rightInner : j ≫ iter inner = iter g ≫ passLeft := by
    have square :
        (g ≫ coprod.map passLeft (𝟙 (ofType (Φ := Φ) D))) ≫ coprod.map (𝟙 (Y ⨿ S)) j = j ≫ inner := by
      simp only [inner, ← Category.assoc j, sideRight, Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp
    exact (iterate_uniformity_ofConstructorReturn (inr_constructor (Φ := Φ) A D) _ inner square).symm.trans
      (iterate_naturality g passLeft).symm
  have innerDecodes : coprod.map passLeft j ≫
      coprod.desc (𝟙 (Y ⨿ S)) (iter inner) =
        coprod.desc (𝟙 (Y ⨿ ofType A)) (iter g) ≫ passLeft := by
    apply coprod.hom_ext
    · simp
    · simp [rightInner]
  have leftInner : i ≫ iter inner = leftBody ≫ passLeft := by
    have entry : i ≫ inner = f ≫ coprod.map passLeft j := by
      change i ≫ (sides ≫ _) = _
      rw [← Category.assoc, sideLeft]
    calc
      _ = i ≫ (inner ≫ coprod.desc (𝟙 (Y ⨿ S)) (iter inner)) :=
        congrArg (i ≫ ·) (iterate_fixpoint inner)
      _ = f ≫ (coprod.map passLeft j ≫ coprod.desc (𝟙 (Y ⨿ S)) (iter inner)) := by
        rw [← Category.assoc, entry, Category.assoc]
      _ = _ := by rw [innerDecodes, ← Category.assoc]
  have leftOuter : i ≫ iter (iter inner) = iter leftBody :=
    (iterate_uniformity_ofConstructorReturn (inl_constructor (Φ := Φ) A D) leftBody (iter inner)
      leftInner.symm).symm
  have outerDecodes : passLeft ≫ coprod.desc (𝟙 Y) (iter (iter inner)) =
      coprod.desc (𝟙 Y) (iter leftBody) := by
    apply coprod.hom_ext
    · simp [passLeft]
    · simp [passLeft, leftOuter]
  have rightOuter : j ≫ iter (iter inner) = iter g ≫ coprod.desc (𝟙 Y) (iter leftBody) := by
    conv_lhs => rw [iterate_fixpoint (iter inner)]
    rw [← Category.assoc, rightInner, Category.assoc, outerDecodes]
  have flatten : inner ≫ coprod.desc (𝟙 (Y ⨿ S)) coprod.inr = sides ≫ joinBlockExits A D Y := by
    simp only [inner, Category.assoc]
    congr 1
    rw [map_desc]
    simp [joinBlockExits, passLeft, i, j, -coprod.desc_comp_inl_comp_inr]
    rfl
  change iter (sides ≫ joinBlockExits A D Y) =
    blockCopair (iter leftBody) (iter g ≫ coprod.desc (𝟙 Y) (iter leftBody))
  rw [← flatten, ← iterate_codiagonal]
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit A D)
  · simpa only [inl_blockCopair] using leftOuter
  · simpa only [inr_blockCopair] using rightOuter

theorem eliminateBlocks_eq_iterate (R : LCtx τ) {Y : Comp}
    (step : ofType (packedExitType R) ⟶ Y ⨿ ofType (packedExitType R)) :
    eliminateBlocks R step = iter step := by
  induction R generalizing Y with
  | nil => exact emptyHom_ext _ _
  | cons A tail ih =>
    let D := packedExitType tail
    let split := step ≫ splitBlockExits A D Y
    let f := (sumCofan A D).inl ≫ split
    let g := (sumCofan A D).inr ≫ split
    have eq : blockCopair f g ≫ joinBlockExits A D Y = step := by
      apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit A D)
      · simp [f, split, split_join]
        erw [Category.comp_id]
      · simp [g, split, split_join]
        erw [Category.comp_id]
    have loop := iterate_join_blocks A D Y f g
    rw [eq] at loop
    change blockCopair _ _ = _
    rw [ih g, loop]
    simp only [f, split, D, Category.assoc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BlockElimination
