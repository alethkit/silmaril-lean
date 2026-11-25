module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Defs

/-! # Transporting interchange and copying to the singleton quotient -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionValues

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Comp" => Paper.TypeCategory (τ := τ) Φ
set_option hygiene false in
local notation "P" => projection Seed

set_option backward.isDefEq.respectTransparency false in
theorem map_pairArrows {X A B : Comp} (f : X ⟶ A) (g : X ⟶ B) :
    (P).map (Paper.TypeCategory.pairArrows (τ := τ) f g) =
      pairArrows Seed ((P).map f) ((P).map g) := by
  change (P).map (Paper.TypeCategory.pairArrows (τ := τ) f g) =
    (P).map (Paper.TypeCategory.diagonalArrow (show τ from X)) ≫
      (whiskerRightFunctor Seed ((P).obj X)).map ((P).map f) ≫
      (whiskerLeftFunctor Seed ((P).obj A)).map ((P).map g)
  rw [whiskerRight_map, whiskerLeft_map, ← (P).map_comp, ← (P).map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem map_centralCopies {A B : Comp} {f : A ⟶ B}
    (hf : Paper.TypeCategory.CentralCopies f) :
    CentralCopies Seed ((P).map f) := by
  constructor
  · intro ⟨X⟩ ⟨Y⟩ g
    obtain ⟨h, rfl⟩ := (P).map_surjective (X := X) (Y := Y) g
    obtain ⟨left, right⟩ := hf.1 h
    constructor
    · change (whiskerRightFunctor Seed ((P).obj X)).map ((P).map f) ≫
          (whiskerLeftFunctor Seed ((P).obj B)).map ((P).map h) =
        (whiskerLeftFunctor Seed ((P).obj A)).map ((P).map h) ≫
          (whiskerRightFunctor Seed ((P).obj Y)).map ((P).map f)
      rw [whiskerRight_map, whiskerLeft_map, whiskerLeft_map, whiskerRight_map,
        ← (P).map_comp, ← (P).map_comp, left]
    · change (whiskerLeftFunctor Seed ((P).obj X)).map ((P).map f) ≫
          (whiskerRightFunctor Seed ((P).obj B)).map ((P).map h) =
        (whiskerRightFunctor Seed ((P).obj A)).map ((P).map h) ≫
          (whiskerLeftFunctor Seed ((P).obj Y)).map ((P).map f)
      rw [whiskerLeft_map, whiskerRight_map, whiskerRight_map, whiskerLeft_map,
        ← (P).map_comp, ← (P).map_comp, right]
  · rw [← map_pairArrows Seed, hf.2, (P).map_comp]
    rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionValues
