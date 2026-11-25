module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Tensor.Thms

/-! # Identity and composition for whiskering on singleton classes -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonTensor

open CategoryTheory Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Region.Paper (TypeCategory whiskerLeftRegion_id whiskerRightRegion_id
  whiskerLeftRegion_comp whiskerRightRegion_comp)
open Region.Paper.TypeCategory
open Region.CfgEta.TypeCategory (whiskerLeftRegion_typed whiskerRightRegion_typed)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ

private theorem comp_typed {A B C : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [B] s [C]) :
    ValueBranches [A] (compLSubst (fun _ => r) (fun _ => s) 0) [C] := by
  have h₁ : LSubst.ValueFamily [] [A] [B] (fun _ => r) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hr
  have h₂ : LSubst.ValueFamily [] [B] [C] (fun _ => s) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hs
  exact (h₁.comp h₂) (ℓ := 0) rfl

theorem whiskerLeft_id (X Y : Comp) :
    whiskerLeft X (𝟙 Y) = 𝟙 (tensorObj X Y) := by
  change whiskerLeft (ofType (show τ from X)) (𝟙 (ofType (show τ from Y))) = _
  rw [← ofRegion_id (show τ from Y), whiskerLeft_ofRegion]
  exact ((ofRegion_eq_iff _ _).mpr (whiskerLeftRegion_id (show τ from X) (show τ from Y))).trans
    (ofRegion_id _)

theorem whiskerRight_id (X Y : Comp) :
    whiskerRight (𝟙 Y) X = 𝟙 (tensorObj Y X) := by
  change whiskerRight (𝟙 (ofType (show τ from Y))) (ofType (show τ from X)) = _
  rw [← ofRegion_id (show τ from Y), whiskerRight_ofRegion]
  exact ((ofRegion_eq_iff _ _).mpr (whiskerRightRegion_id (show τ from X) (show τ from Y))).trans
    (ofRegion_id _)

theorem whiskerLeft_comp (X : Comp) {A B C : Comp} (f : A ⟶ B) (g : B ⟶ C) :
    whiskerLeft X (f ≫ g) = whiskerLeft X f ≫ whiskerLeft X g := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion (A := (show τ from A)) (B := (show τ from B)) f
  obtain ⟨s, hs, rfl⟩ := exists_ofRegion (A := (show τ from B)) (B := (show τ from C)) g
  let x : τ := X
  change whiskerLeft (ofType x) _ = _
  rw [ofRegion_comp hr hs (comp_typed hr hs), whiskerLeft_ofRegion]
  change _ = whiskerLeft (ofType x) (ofRegion hr) ≫ whiskerLeft (ofType x) (ofRegion hs)
  rw [whiskerLeft_ofRegion, whiskerLeft_ofRegion]
  unfold tensorObj
  rw [ofRegion_comp _ _ (comp_typed (whiskerLeftRegion_typed x hr) (whiskerLeftRegion_typed x hs))]
  exact (ofRegion_eq_iff _ _).mpr (whiskerLeftRegion_comp x hr hs).symm

theorem whiskerRight_comp (X : Comp) {A B C : Comp} (f : A ⟶ B) (g : B ⟶ C) :
    whiskerRight (f ≫ g) X = whiskerRight f X ≫ whiskerRight g X := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion (A := (show τ from A)) (B := (show τ from B)) f
  obtain ⟨s, hs, rfl⟩ := exists_ofRegion (A := (show τ from B)) (B := (show τ from C)) g
  let x : τ := X
  change whiskerRight _ (ofType x) = _
  rw [ofRegion_comp hr hs (comp_typed hr hs), whiskerRight_ofRegion]
  change _ = whiskerRight (ofRegion hr) (ofType x) ≫ whiskerRight (ofRegion hs) (ofType x)
  rw [whiskerRight_ofRegion, whiskerRight_ofRegion]
  unfold tensorObj
  rw [ofRegion_comp _ _ (comp_typed (whiskerRightRegion_typed x hr) (whiskerRightRegion_typed x hs))]
  exact (ofRegion_eq_iff _ _).mpr (whiskerRightRegion_comp x hr hs).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonTensor
