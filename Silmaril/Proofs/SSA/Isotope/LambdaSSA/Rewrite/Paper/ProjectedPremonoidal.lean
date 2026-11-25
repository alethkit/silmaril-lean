module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Unit.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Defs

/-! # Descent of guarded associator, braid, and unit laws -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.Extension.Singleton

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

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (centralCopies_associate centralCopies_braid associate_pentagon
  braid_hexagon_forward braid_hexagon_reverse unitProjection_triangle leftUnitProjection rightUnitProjection
  leftUnitSection rightUnitSection leftUnit_section_projection rightUnit_section_projection
  leftUnit_projection_section rightUnit_projection_section centralCopies_productFst centralCopies_productSnd
  associate_whiskerRight_right associate_whiskerLeft_right associate_whiskerLeft_left
  whiskerRight_braid whiskerLeft_braid whiskerLeft_productSnd whiskerRight_productFst braid_braid)

local notation "α" => associateIso Seed
local notation "β" => braidIso Seed

local notation "oldDiscard" => Paper.TypeCategory.discardArrow (Φ := Φ) U

set_option backward.isDefEq.respectTransparency false

theorem associate_central (A B C : Q) : WhiskerCentral Seed (α A B C).hom :=
  fun {_ _} g => (map_centralCopies Seed (centralCopies_associate (show τ from A.as) (show τ from B.as) (show τ from C.as))).1 g

theorem braid_central (A B : Q) : WhiskerCentral Seed (β A B).hom :=
  fun {_ _} g => (map_centralCopies Seed (centralCopies_braid (show τ from A.as) (show τ from B.as))).1 g

theorem pentagon (A B C D : Q) :
    R (α A B C).hom D ≫ (α A (T B C) D).hom ≫ L A (α B C D).hom =
      (α (T A B) C D).hom ≫ (α A B (T C D)).hom := by
  simpa only [Functor.map_comp, ← whiskerLeft_map, ← whiskerRight_map] using!
    congrArg (fun f => (P).map f) (associate_pentagon (Φ := Φ)
      (show τ from A.as) (show τ from B.as) (show τ from C.as) (show τ from D.as))

theorem hexagon_forward (A B C : Q) :
    (α A B C).hom ≫ (β A (T B C)).hom ≫ (α B C A).hom =
      R (β A B).hom C ≫ (α B A C).hom ≫ L B (β A C).hom := by
  simpa only [Functor.map_comp, ← whiskerLeft_map, ← whiskerRight_map] using!
    congrArg (fun f => (P).map f) (braid_hexagon_forward (Φ := Φ)
      (show τ from A.as) (show τ from B.as) (show τ from C.as))

theorem hexagon_reverse (A B C : Q) :
    (α A B C).inv ≫ (β (T A B) C).hom ≫ (α C A B).inv =
      L A (β B C).hom ≫ (α A C B).inv ≫ R (β A C).hom B := by
  simpa only [Functor.map_comp, ← whiskerLeft_map, ← whiskerRight_map] using!
    congrArg (fun f => (P).map f) (braid_hexagon_reverse (Φ := Φ)
      (show τ from A.as) (show τ from B.as) (show τ from C.as))

theorem associate_naturality_left {A B : Q} (f : A ⟶ B) (X Y : Q) :
    R (R f X) Y ≫ (α B X Y).hom = (α A X Y).hom ≫ R f (T X Y) := by
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := A.as) (Y := B.as) f
  simpa only [Functor.map_comp, ← whiskerRight_map] using!
    congrArg (fun k => (P).map k) (associate_whiskerRight_right (show τ from X.as) (show τ from Y.as) f)

theorem associate_naturality_middle {A B : Q} (f : A ⟶ B) (X Y : Q) :
    R (L X f) Y ≫ (α X B Y).hom = (α X A Y).hom ≫ L X (R f Y) := by
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := A.as) (Y := B.as) f
  simpa only [Functor.map_comp, ← whiskerLeft_map, ← whiskerRight_map] using!
    congrArg (fun k => (P).map k) (associate_whiskerLeft_right (show τ from X.as) (show τ from Y.as) f)

theorem associate_naturality_right {A B : Q} (f : A ⟶ B) (X Y : Q) :
    L (T X Y) f ≫ (α X Y B).hom = (α X Y A).hom ≫ L X (L Y f) := by
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := A.as) (Y := B.as) f
  simpa only [Functor.map_comp, ← whiskerLeft_map] using!
    congrArg (fun k => (P).map k) (associate_whiskerLeft_left (show τ from X.as) (show τ from Y.as) f)

theorem braid_naturality_left {A B : Q} (f : A ⟶ B) (X : Q) :
    R f X ≫ (β B X).hom = (β A X).hom ≫ L X f := by
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := A.as) (Y := B.as) f
  simpa only [Functor.map_comp, ← whiskerLeft_map, ← whiskerRight_map] using!
    congrArg (fun k => (P).map k) (whiskerRight_braid (show τ from X.as) f)

theorem braid_naturality_right {A B : Q} (f : A ⟶ B) (X : Q) :
    L X f ≫ (β X B).hom = (β X A).hom ≫ R f X := by
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := A.as) (Y := B.as) f
  simpa only [Functor.map_comp, ← whiskerLeft_map, ← whiskerRight_map] using!
    congrArg (fun k => (P).map k) (whiskerLeft_braid (show τ from X.as) f)

theorem triangle (X Y : Q) :
    (α X (Obj U) Y).hom ≫ L X (unitProjectionLeft Seed Y) = R (unitProjectionRight Seed X) Y := by
  simpa only [Functor.map_comp, ← whiskerLeft_map, ← whiskerRight_map] using!
    congrArg (fun k => (P).map k) (unitProjection_triangle (Φ := Φ) (show τ from X.as) (show τ from Y.as))

theorem unit_eta
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {K : LCtx τ}, Paper.WithUnitEta.Step Γ r s K → Seed Γ r s K) :
    (P).map oldDiscard = 𝟙 (Obj U) := by
  rw [← (P).map_id, ← Paper.TypeCategory.ofRegion_id]
  exact (ofRegion_eq_iff Seed _ _).2 (.extra (.br rfl .unit) (.br rfl (.var rfl)) (includeUnit .unit))

theorem leftUnit_hom_inv (h : (P).map oldDiscard = 𝟙 (Obj U)) (X : Q) :
    unitProjectionLeft Seed X ≫ (P).map (leftUnitSection (show τ from X.as)) =
      𝟙 (T (Obj U) X) := by
  change (P).map (leftUnitProjection _) ≫ (P).map (leftUnitSection _) = _
  rw [← (P).map_comp, leftUnit_projection_section, ← whiskerRight_map, h]
  exact (whiskerRightFunctor Seed X).map_id (Obj U)

theorem leftUnit_inv_hom (X : Q) :
    (P).map (leftUnitSection (show τ from X.as)) ≫ unitProjectionLeft Seed X = 𝟙 X := by
  change (P).map (leftUnitSection _) ≫ (P).map (leftUnitProjection _) = _
  rw [← (P).map_comp, leftUnit_section_projection, (P).map_id]
  rfl

theorem rightUnit_hom_inv (h : (P).map oldDiscard = 𝟙 (Obj U)) (X : Q) :
    unitProjectionRight Seed X ≫ (P).map (rightUnitSection (show τ from X.as)) =
      𝟙 (T X (Obj U)) := by
  change (P).map (rightUnitProjection _) ≫ (P).map (rightUnitSection _) = _
  rw [← (P).map_comp, rightUnit_projection_section, ← whiskerLeft_map, h]
  exact (whiskerLeftFunctor Seed X).map_id (Obj U)

theorem rightUnit_inv_hom (X : Q) :
    (P).map (rightUnitSection (show τ from X.as)) ≫ unitProjectionRight Seed X = 𝟙 X := by
  change (P).map (rightUnitSection _) ≫ (P).map (rightUnitProjection _) = _
  rw [← (P).map_comp, rightUnit_section_projection, (P).map_id]
  rfl

theorem leftUnit_naturality {X Y : Q} (f : X ⟶ Y) :
    L (Obj U) f ≫ unitProjectionLeft Seed Y = unitProjectionLeft Seed X ≫ f := by
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := X.as) (Y := Y.as) f
  simpa only [Functor.map_comp, ← whiskerLeft_map] using!
    congrArg (fun k => (P).map k) (whiskerLeft_productSnd U f)

theorem rightUnit_naturality {X Y : Q} (f : X ⟶ Y) :
    R f (Obj U) ≫ unitProjectionRight Seed Y = unitProjectionRight Seed X ≫ f := by
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := X.as) (Y := Y.as) f
  simpa only [Functor.map_comp, ← whiskerRight_map] using!
    congrArg (fun k => (P).map k) (whiskerRight_productFst U f)

theorem leftUnit_central (X : Q) : WhiskerCentral Seed (unitProjectionLeft Seed X) :=
  fun {_ _} g => (map_centralCopies Seed (centralCopies_productSnd (Φ := Φ) U (show τ from X.as))).1 g

theorem rightUnit_central (X : Q) : WhiskerCentral Seed (unitProjectionRight Seed X) :=
  fun {_ _} g => (map_centralCopies Seed (centralCopies_productFst (Φ := Φ) (show τ from X.as) U)).1 g

theorem braid_symmetry (X Y : Q) : (β X Y).hom ≫ (β Y X).hom = 𝟙 (T X Y) := by
  simpa only [Functor.map_comp, Functor.map_id] using!
    congrArg (fun f => (P).map f) (braid_braid (Φ := Φ) (show τ from X.as) (show τ from Y.as))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedPremonoidal
