module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Thms

/-! # Intrinsic closure of central, copying, discard-preserving arrows -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.Extension.Singleton
open Paper.Extension.Singleton.StructuralValues (HomProperty)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "L" => whiskerLeft Seed
local notation "R" => whiskerRight Seed
local notation "δ" => diagonalArrow Seed
local notation "pair" => pairArrows Seed

private theorem lc (X : Q) {Y Z W : Q} (f : Y ⟶ Z) (g : Z ⟶ W) :
    L X (f ≫ g) = L X f ≫ L X g := (whiskerLeftFunctor Seed X).map_comp f g

private theorem rc (X : Q) {Y Z W : Q} (f : Y ⟶ Z) (g : Z ⟶ W) :
    R (f ≫ g) X = R f X ≫ R g X := (whiskerRightFunctor Seed X).map_comp f g

private theorem li (X Y : Q) : L X (𝟙 Y) = 𝟙 _ := (whiskerLeftFunctor Seed X).map_id Y

private theorem ri (X Y : Q) : R (𝟙 Y) X = 𝟙 _ := (whiskerRightFunctor Seed X).map_id Y

theorem pair_comp {X Y A B : Q} (f : X ⟶ Y) (g : Y ⟶ A) (h : Y ⟶ B)
    (hf : CentralCopies Seed f) : pair (f ≫ g) (f ≫ h) = f ≫ pair g h := by
  calc
    _ = pair f f ≫ (R g Y ≫ L A h) := by
      simp only [pairArrows, lc, rc, Category.assoc]
      rw [← Category.assoc (R g X), ← (hf.1 g).2, Category.assoc]
    _ = _ := by
      rw [show pair f f = f ≫ δ Y from hf.2, Category.assoc]
      rfl

theorem id_mem (X : Q) : HomProperty Seed (𝟙 X) := by
  refine ⟨⟨?_, ?_⟩, Category.id_comp _⟩
  · intro A B g
    simp only [li, ri, Category.id_comp, Category.comp_id, and_self]
  ·
    simp only [pairArrows, li, ri, Category.comp_id, Category.id_comp]

theorem comp_mem {X Y Z : Q} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HomProperty Seed f) (hg : HomProperty Seed g) : HomProperty Seed (f ≫ g) := by
  refine ⟨⟨?_, ?_⟩, (Category.assoc _ _ _).trans ((congrArg (f ≫ ·) hg.2).trans hf.2)⟩
  · intro A B h
    constructor
    · simp only [rc, Category.assoc, (hg.1.1 h).1]
      rw [← Category.assoc, (hf.1.1 h).1, Category.assoc]
    · simp only [lc, Category.assoc, (hg.1.1 h).2]
      rw [← Category.assoc, (hf.1.1 h).2, Category.assoc]
  ·
    rw [pair_comp Seed f g g hf.1, show pair g g = g ≫ δ Z from hg.1.2, Category.assoc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValues
