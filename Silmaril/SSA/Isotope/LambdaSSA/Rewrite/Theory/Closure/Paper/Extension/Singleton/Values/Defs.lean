module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Thms

/-! # Projected value arrows in an extended Paper singleton quotient -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "Q" => TypeCategory Seed

/-- The product type of the two underlying syntactic objects. -/
abbrev tensorObj (X Y : Q) : Q :=
  (projection Seed).obj (Paper.TypeCategory.tensorObj X.as Y.as)

abbrev whiskerLeft (X : Q) {Y Z : Q} (f : Y ⟶ Z) :
    tensorObj Seed X Y ⟶ tensorObj Seed X Z :=
  (whiskerLeftFunctor Seed X).map f

abbrev whiskerRight {Y Z : Q} (f : Y ⟶ Z) (X : Q) :
    tensorObj Seed Y X ⟶ tensorObj Seed Z X :=
  (whiskerRightFunctor Seed X).map f

/-- Project the literal constructor diagonal. -/
def diagonalArrow (X : Q) : X ⟶ tensorObj Seed X X :=
  (projection Seed).map (Paper.TypeCategory.diagonalArrow (show τ from X.as))

/-- Pair using the projected diagonal and the two fixed-factor actions. -/
def pairArrows {X A B : Q} (f : X ⟶ A) (g : X ⟶ B) : X ⟶ tensorObj Seed A B :=
  diagonalArrow Seed X ≫ whiskerRight Seed f X ≫ whiskerLeft Seed A g

/-- Interchange against all arrows of the extended quotient. -/
def WhiskerCentral {A B : Q} (f : A ⟶ B) : Prop :=
  ∀ {X Y : Q} (g : X ⟶ Y),
    (whiskerRight Seed f X ≫ whiskerLeft Seed B g = whiskerLeft Seed A g ≫ whiskerRight Seed f Y) ∧
    (whiskerLeft Seed X f ≫ whiskerRight Seed g B = whiskerRight Seed g A ≫ whiskerLeft Seed Y f)

/-- Interchange and diagonal preservation in the extended quotient. -/
def CentralCopies : MorphismProperty Q := fun _ B f =>
  WhiskerCentral Seed f ∧ pairArrows Seed f f = f ≫ diagonalArrow Seed B

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The image of an exactly typed pure return in the extended quotient. -/
def ProjectedPureReturn : MorphismProperty Q := fun X Y f =>
  ∃ g : X.as ⟶ Y.as, Paper.TypeCategory.PureReturn pe g ∧ (projection Seed).map g = f

/-- A projected pure return with a central, diagonal-preserving lift. The two
witnesses can come from different default arrows identified by the quotient. -/
def ProjectedCopyingReturn : MorphismProperty Q := fun X Y f =>
  ProjectedPureReturn Seed pe f ∧
    ∃ g : X.as ⟶ Y.as, Paper.TypeCategory.CentralCopies g ∧ (projection Seed).map g = f

set_option backward.isDefEq.respectTransparency false in
instance projectedCopyingReturn_multiplicative : (ProjectedCopyingReturn Seed pe).IsMultiplicative where
  id_mem X := by
    have h := (Paper.TypeCategory.CopyingPureReturn (τ := τ) (Φ := Φ) pe).id_mem X.as
    exact ⟨⟨_, h.1.1, (projection Seed).map_id X.as⟩, ⟨_, ⟨h.1.2, h.2⟩, (projection Seed).map_id X.as⟩⟩
  comp_mem f g hf hg := by
    obtain ⟨⟨f₁, pf, hf₁⟩, ⟨f₂, cf, hf₂⟩⟩ := hf
    obtain ⟨⟨g₁, pg, hg₁⟩, ⟨g₂, cg, hg₂⟩⟩ := hg
    refine ⟨⟨f₁ ≫ g₁, Paper.TypeCategory.pureReturn_comp pe pf pg, ?_⟩,
      ⟨f₂ ≫ g₂, ⟨Paper.TypeCategory.WhiskerCentral.comp cf.1 cg.1, Paper.TypeCategory.pairArrows_copy_comp (τ := τ) f₂ g₂ cf.1 cf.2 cg.2⟩, ?_⟩⟩
    · rw [(projection Seed).map_comp, hf₁, hg₁]
    · rw [(projection Seed).map_comp, hf₂, hg₂]

/-- Projected pure returns with a central, diagonal-preserving lift form a wide subcategory. -/
abbrev ProjectedCopyingValueCategory := WideSubcategory (ProjectedCopyingReturn Seed pe)

/-- Include the projected value arrows into the extended computation quotient. -/
abbrev copyingValues : ProjectedCopyingValueCategory Seed pe ⥤ Q :=
  wideSubcategoryInclusion _

instance copyingValues_faithful : (copyingValues Seed pe).Faithful :=
  inferInstanceAs (wideSubcategoryInclusion _).Faithful

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
