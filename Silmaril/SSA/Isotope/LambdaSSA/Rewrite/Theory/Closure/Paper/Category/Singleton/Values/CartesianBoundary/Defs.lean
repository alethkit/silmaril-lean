module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Copy.Thms
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan

/-! # Copying and discard in the Paper singleton category -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches productSndBranches)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ
local notation "paperObj" => ofType (τ := τ) (Φ := Φ)

/-- The literal constructor return of unit. -/
def discardArrow (X : τ) : paperObj X ⟶ paperObj (Silmaril.unit : τ) :=
  ofRegion (.br (ℓ := 0) rfl (.unit (Γ := [X])))

/-- Discarding the result of the arrow agrees with discarding its input. -/
def PreservesDiscard : MorphismProperty Comp :=
  fun X Y f => f ≫ discardArrow (τ := τ) (Φ := Φ) Y = discardArrow (τ := τ) (Φ := Φ) X

instance preservesDiscard_multiplicative : (PreservesDiscard (τ := τ) (Φ := Φ)).IsMultiplicative where
  id_mem X := Category.id_comp (discardArrow (τ := τ) (Φ := Φ) X)
  comp_mem f g hf hg := by
    change (f ≫ g) ≫ discardArrow (τ := τ) (Φ := Φ) _ = _
    rw [Category.assoc, hg, hf]

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Central pure returns whose sequential self-pairing agrees with copying their result. -/
def CopyingPureReturn : MorphismProperty Comp :=
  fun _ _ f => CentralPureReturn pe f ∧ PreservesDiagonal f

set_option backward.isDefEq.respectTransparency false in
instance copyingPureReturn_multiplicative :
    (CopyingPureReturn (τ := τ) (Φ := Φ) pe).IsMultiplicative where
  id_mem X := ⟨(CentralPureReturn (τ := τ) (Φ := Φ) pe).id_mem X, by
    change pairArrows (τ := τ) (𝟙 X) (𝟙 X) = 𝟙 X ≫ diagonalArrow (show τ from X)
    simp [pairArrows, whiskerRight_id, whiskerLeft_id, tensorObj]⟩
  comp_mem f g hf hg := ⟨(CentralPureReturn (τ := τ) (Φ := Φ) pe).comp_mem f g hf.1 hg.1,
    pairArrows_copy_comp (τ := τ) f g hf.1.2 hf.2 hg.2⟩

/-- The wide subcategory of central pure returns that preserve the diagonal. -/
abbrev CopyingValueCategory := WideSubcategory (CopyingPureReturn (τ := τ) (Φ := Φ) pe)

/-- Include the diagonal-preserving pure returns among all central pure returns. -/
def copyingToCentral : CopyingValueCategory (τ := τ) (Φ := Φ) pe ⥤
    CentralValueCategory (τ := τ) (Φ := Φ) pe where
  obj X := ⟨X.obj⟩
  map f := ⟨f.1, f.2.1⟩

instance copyingToCentral_faithful : (copyingToCentral (τ := τ) (Φ := Φ) pe).Faithful where
  map_injective h := WideSubcategory.hom_ext _ (congrArg (·.1) h)

set_option hygiene false in
local notation "Values" => CopyingValueCategory (τ := τ) (Φ := Φ) pe

/-- The chosen syntax projections, whenever both belong to the copying value category. -/
def copyingProductFan (A B : τ)
    (fst : CopyingPureReturn pe (ofRegion (τ := τ) (productFstBranches (Φ := Φ) A B)))
    (snd : CopyingPureReturn pe (ofRegion (τ := τ) (productSndBranches (Φ := Φ) A B))) :
    BinaryFan (⟨paperObj A⟩ : Values) (⟨paperObj B⟩ : Values) :=
  BinaryFan.mk (P := (⟨paperObj (product A B)⟩ : Values))
    ⟨ofRegion (τ := τ) (productFstBranches A B), fst⟩ ⟨ofRegion (τ := τ) (productSndBranches A B), snd⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
