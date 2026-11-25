module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Defs
public import Silmaril.Semantics.Categories.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal

/-! # Premonoidal structure in singleton quotients with unit η -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open scoped MonoidalCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (leftUnitSection rightUnitSection)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "P" => projection Seed
local notation "U" => (Silmaril.unit : τ)
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "T" => tensorObj Seed
local notation "L" => whiskerLeft Seed
local notation "R" => whiskerRight Seed

local notation "α" => associateIso Seed
local notation "β" => braidIso Seed

local notation "oldDiscard" => Paper.TypeCategory.discardArrow (Φ := Φ) U

theorem associate_central (A B C : Q) : WhiskerCentral Seed (α A B C).hom :=
  fun {_ _} g => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.associate_central Seed A B C g

theorem braid_central (A B : Q) : WhiskerCentral Seed (β A B).hom :=
  fun {_ _} g => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.braid_central Seed A B g

theorem pentagon (A B C D : Q) :
    R (α A B C).hom D ≫ (α A (T B C) D).hom ≫ L A (α B C D).hom =
      (α (T A B) C D).hom ≫ (α A B (T C D)).hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.pentagon Seed A B C D

theorem hexagon_forward (A B C : Q) :
    (α A B C).hom ≫ (β A (T B C)).hom ≫ (α B C A).hom =
      R (β A B).hom C ≫ (α B A C).hom ≫ L B (β A C).hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.hexagon_forward Seed A B C

theorem hexagon_reverse (A B C : Q) :
    (α A B C).inv ≫ (β (T A B) C).hom ≫ (α C A B).inv =
      L A (β B C).hom ≫ (α A C B).inv ≫ R (β A C).hom B :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.hexagon_reverse Seed A B C

theorem associate_naturality_left {A B : Q} (f : A ⟶ B) (X Y : Q) :
    R (R f X) Y ≫ (α B X Y).hom = (α A X Y).hom ≫ R f (T X Y) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.associate_naturality_left Seed f X Y

theorem associate_naturality_middle {A B : Q} (f : A ⟶ B) (X Y : Q) :
    R (L X f) Y ≫ (α X B Y).hom = (α X A Y).hom ≫ L X (R f Y) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.associate_naturality_middle Seed f X Y

theorem associate_naturality_right {A B : Q} (f : A ⟶ B) (X Y : Q) :
    L (T X Y) f ≫ (α X Y B).hom = (α X Y A).hom ≫ L X (L Y f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.associate_naturality_right Seed f X Y

theorem braid_naturality_left {A B : Q} (f : A ⟶ B) (X : Q) :
    R f X ≫ (β B X).hom = (β A X).hom ≫ L X f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.braid_naturality_left Seed f X

theorem braid_naturality_right {A B : Q} (f : A ⟶ B) (X : Q) :
    L X f ≫ (β X B).hom = (β X A).hom ≫ R f X :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.braid_naturality_right Seed f X

theorem triangle (X Y : Q) :
    (α X (Obj U) Y).hom ≫ L X (unitProjectionLeft Seed Y) = R (unitProjectionRight Seed X) Y :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.triangle Seed X Y

theorem unit_eta_of_include
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {K : LCtx τ}, Paper.WithUnitEta.Step Γ r s K → Seed Γ r s K) :
    (P).map oldDiscard = 𝟙 (Obj U) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.unit_eta Seed includeUnit

theorem leftUnit_naturality {X Y : Q} (f : X ⟶ Y) :
    L (Obj U) f ≫ unitProjectionLeft Seed Y = unitProjectionLeft Seed X ≫ f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.leftUnit_naturality Seed f

theorem rightUnit_naturality {X Y : Q} (f : X ⟶ Y) :
    R f (Obj U) ≫ unitProjectionRight Seed Y = unitProjectionRight Seed X ≫ f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.rightUnit_naturality Seed f

theorem leftUnit_central (X : Q) : WhiskerCentral Seed (unitProjectionLeft Seed X) :=
  fun {_ _} g => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.leftUnit_central Seed X g

theorem rightUnit_central (X : Q) : WhiskerCentral Seed (unitProjectionRight Seed X) :=
  fun {_ _} g => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.rightUnit_central Seed X g

theorem braid_symmetry (X Y : Q) : (β X Y).hom ≫ (β Y X).hom = 𝟙 (T X Y) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.braid_symmetry Seed X Y

theorem leftUnit_hom_inv (h : (P).map oldDiscard = 𝟙 (Obj U)) (X : Q) :
    unitProjectionLeft Seed X ≫ (P).map (leftUnitSection (show τ from X.as)) =
      𝟙 (T (Obj U) X) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.leftUnit_hom_inv Seed h X

theorem leftUnit_inv_hom (X : Q) :
    (P).map (leftUnitSection (show τ from X.as)) ≫ unitProjectionLeft Seed X = 𝟙 X :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.leftUnit_inv_hom Seed X

theorem rightUnit_hom_inv (h : (P).map oldDiscard = 𝟙 (Obj U)) (X : Q) :
    unitProjectionRight Seed X ≫ (P).map (rightUnitSection (show τ from X.as)) =
      𝟙 (T X (Obj U)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.rightUnit_hom_inv Seed h X

theorem rightUnit_inv_hom (X : Q) :
    (P).map (rightUnitSection (show τ from X.as)) ≫ unitProjectionRight Seed X = 𝟙 X :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal.rightUnit_inv_hom Seed X

/-- Insert literal unit as the inverse of the guarded left projection. -/
@[expose] def leftUnitIsoOfEta (h : (P).map oldDiscard = 𝟙 (Obj U)) (X : Q) : T (Obj U) X ≅ X where
  hom := unitProjectionLeft Seed X
  inv := (P).map (leftUnitSection (show τ from X.as))
  hom_inv_id := leftUnit_hom_inv Seed h X
  inv_hom_id := leftUnit_inv_hom Seed X

/-- Insert literal unit as the inverse of the guarded right projection. -/
@[expose] def rightUnitIsoOfEta (h : (P).map oldDiscard = 𝟙 (Obj U)) (X : Q) : T X (Obj U) ≅ X where
  hom := unitProjectionRight Seed X
  inv := (P).map (rightUnitSection (show τ from X.as))
  hom_inv_id := rightUnit_hom_inv Seed h X
  inv_hom_id := rightUnit_inv_hom Seed X

/-- The existing fixed-factor actions with guarded associativity and unit η as a premonoidal category. -/
abbrev premonoidalOfUnitEta
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {K : LCtx τ}, Paper.WithUnitEta.Step Γ r s K → Seed Γ r s K) : PremonoidalCategory Q where
  tensorObj := T
  whiskerLeft := L
  whiskerRight := R
  tensorUnit := Obj U
  associator := α
  leftUnitor := leftUnitIsoOfEta Seed (unit_eta_of_include Seed includeUnit)
  rightUnitor := rightUnitIsoOfEta Seed (unit_eta_of_include Seed includeUnit)
  tensorHom_def _ _ := rfl
  whiskerLeft_id X Y := (whiskerLeftFunctor Seed X).map_id Y
  whiskerLeft_comp := fun X {_ _ _} f g => (whiskerLeftFunctor Seed X).map_comp f g
  id_whiskerRight X Y := (whiskerRightFunctor Seed Y).map_id X
  comp_whiskerRight f g W := (whiskerRightFunctor Seed W).map_comp f g
  associator_central X Y Z := ⟨fun {_ _} f => (associate_central Seed X Y Z f).1,
    fun {_ _} f => (associate_central Seed X Y Z f).2.symm⟩
  leftUnitor_central X := ⟨fun {_ _} f => (leftUnit_central Seed X f).1,
    fun {_ _} f => (leftUnit_central Seed X f).2.symm⟩
  rightUnitor_central X := ⟨fun {_ _} f => (rightUnit_central Seed X f).1,
    fun {_ _} f => (rightUnit_central Seed X f).2.symm⟩
  associator_naturality_left f X Y := associate_naturality_left Seed f X Y
  associator_naturality_middle := fun X {_ _} f Y => associate_naturality_middle Seed f X Y
  associator_naturality_right := fun X Y {_ _} f => associate_naturality_right Seed f X Y
  leftUnitor_naturality f := leftUnit_naturality Seed f
  rightUnitor_naturality f := rightUnit_naturality Seed f
  pentagon := pentagon Seed
  triangle := triangle Seed

/-- The guarded braid equips the chosen premonoidal structure with symmetry. -/
abbrev symmetricPremonoidalOfUnitEta
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {K : LCtx τ}, Paper.WithUnitEta.Step Γ r s K → Seed Γ r s K) :
    @SymmetricPremonoidalCategory Q _ (premonoidalOfUnitEta Seed includeUnit) := by
  letI := premonoidalOfUnitEta Seed includeUnit
  exact {
    braiding := β
    naturality_left f X := braid_naturality_left Seed f X
    naturality_right := fun X {_ _} f => braid_naturality_right Seed f X
    hexagon_forward := hexagon_forward Seed
    hexagon_reverse := hexagon_reverse Seed
    braiding_central X Y := ⟨fun {_ _} f => (braid_central Seed X Y f).1, fun {_ _} f => (braid_central Seed X Y f).2.symm⟩
    symmetry := braid_symmetry Seed
  }


end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
