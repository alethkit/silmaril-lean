module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Products.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.Interchange.Thms

/-! # Intrinsic product closure from guarded interchange and the diagonal -/

public section

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.Extension.Singleton.StructuralValues

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValueProducts

set_option backward.isDefEq.respectTransparency false

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "Val" => ValueCategory Seed
local notation "incl" => inclusion Seed
local notation "L" => whiskerLeft Seed
local notation "R" => whiskerRight Seed
local notation "d" => discardArrow Seed
local notation "H" => HomProperty Seed
local notation "T" => tensorObj Seed
local notation "proj" => projection Seed
local notation "α" => associateIso Seed
local notation "β" => braidIso Seed
local notation "δ" => diagonalArrow Seed
local notation "pair" => pairArrows Seed
local notation "Centr" => WhiskerCentral Seed
local notation "U" => (Silmaril.unit : τ)
local infixr:70 " ×ₜ " => Silmaril.product

private abbrev tensor {X A Y B : Q} (f : X ⟶ A) (g : Y ⟶ B) : T X Y ⟶ T A B :=
  R f Y ≫ L A g

set_option hygiene false in
local infixr:72 " ⊗ₛ " => tensor Seed

private theorem lc (X : Q) {Y Z W : Q} (f : Y ⟶ Z) (g : Z ⟶ W) :
    L X (f ≫ g) = L X f ≫ L X g := (whiskerLeftFunctor Seed X).map_comp f g

private theorem rc (X : Q) {Y Z W : Q} (f : Y ⟶ Z) (g : Z ⟶ W) :
    R (f ≫ g) X = R f X ≫ R g X := (whiskerRightFunctor Seed X).map_comp f g

private theorem li (X Y : Q) : L X (𝟙 Y) = 𝟙 _ := (whiskerLeftFunctor Seed X).map_id Y
private theorem ri (X Y : Q) : R (𝟙 Y) X = 𝟙 _ := (whiskerRightFunctor Seed X).map_id Y

private theorem tc {X A A' Y B B' : Q} (f : X ⟶ A) (g : Y ⟶ B) (h : A ⟶ A') (k : B ⟶ B')
    (swap : L A g ≫ R h B = R h Y ≫ L A' g) :
    (f ≫ h) ⊗ₛ (g ≫ k) = (f ⊗ₛ g) ≫ (h ⊗ₛ k) := by
  simp only [tensor, lc, rc, Category.assoc]
  rw [← Category.assoc (L A g), swap, Category.assoc]

private theorem assoc_tensor {X A Y B Z C : Q}
    (f : X ⟶ A) (g : Y ⟶ B) (h : Z ⟶ C) :
    ((f ⊗ₛ g) ⊗ₛ h) ≫ (α A B C).hom = (α X Y Z).hom ≫ (f ⊗ₛ (g ⊗ₛ h)) := by
  simp only [tensor, lc, rc, Category.assoc]
  rw [associate_naturality_right Seed, ← Category.assoc (R (L A g) Z),
    associate_naturality_middle Seed, Category.assoc, ← Category.assoc (R (R f Y) Z),
    associate_naturality_left Seed, Category.assoc]

private theorem unassoc_tensor {X A Y B Z C : Q}
    (f : X ⟶ A) (g : Y ⟶ B) (h : Z ⟶ C) :
    (f ⊗ₛ (g ⊗ₛ h)) ≫ (α A B C).inv = (α X Y Z).inv ≫ ((f ⊗ₛ g) ⊗ₛ h) := by
  apply (cancel_mono (α A B C).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, assoc_tensor, Iso.inv_hom_id_assoc]

private theorem braid_tensor {X A Y B : Q}
    (f : X ⟶ A) {g : Y ⟶ B} (hg : Centr g) :
    (f ⊗ₛ g) ≫ (β A B).hom = (β X Y).hom ≫ (g ⊗ₛ f) := by
  simp only [tensor, Category.assoc]
  rw [braid_naturality_right Seed, ← Category.assoc (R f Y),
    braid_naturality_left Seed, Category.assoc, (hg f).1]

private theorem tensor_whiskerLeft {X A Y B B' : Q} (f : X ⟶ A) (g : Y ⟶ B) (h : B ⟶ B') :
    (f ⊗ₛ g) ≫ L A h = f ⊗ₛ (g ≫ h) := by
  simp only [tensor, lc, Category.assoc]

private theorem whiskerLeft_tensor {X A Y B B' : Q} {f : X ⟶ A} (g : Y ⟶ B) (h : B ⟶ B')
    (hf : Centr f) : L X g ≫ (f ⊗ₛ h) = f ⊗ₛ (g ≫ h) := by
  simp only [tensor, lc]
  rw [← Category.assoc, ← (hf g).1, Category.assoc]

private theorem tensor_whiskerRight {X A A' Y B : Q} (f : X ⟶ A) {g : Y ⟶ B} (h : A ⟶ A')
    (hg : Centr g) : (f ⊗ₛ g) ≫ R h B = (f ≫ h) ⊗ₛ g := by
  simp only [tensor, rc, Category.assoc]
  rw [(hg h).2]

private theorem whiskerRight_tensor {X A A' Y B : Q} (f : X ⟶ A) (g : A ⟶ A') (h : Y ⟶ B) :
    R f Y ≫ (g ⊗ₛ h) = (f ≫ g) ⊗ₛ h := by
  simp only [tensor, rc, Category.assoc]

private abbrev swapLeading (A B C : Q) : T A (T B C) ⟶ T B (T A C) :=
  (α A B C).inv ≫ R (β A B).hom C ≫ (α B A C).hom

private theorem swapLeading_natural
    {X A Y B Z C : Q} (f : X ⟶ A) {g : Y ⟶ B} {h : Z ⟶ C}
    (hg : Centr g) (hh : Centr h) :
    (f ⊗ₛ (g ⊗ₛ h)) ≫ swapLeading Seed A B C =
      swapLeading Seed X Y Z ≫ (g ⊗ₛ (f ⊗ₛ h)) := by
  unfold swapLeading
  rw [← Category.assoc (f ⊗ₛ (g ⊗ₛ h)), unassoc_tensor, Category.assoc,
    ← Category.assoc ((f ⊗ₛ g) ⊗ₛ h), tensor_whiskerRight Seed _ _ hh,
    braid_tensor Seed f hg, ← whiskerRight_tensor, Category.assoc, assoc_tensor]
  simp only [Category.assoc]

private abbrev shuffle (X Y Z W : Q) : T (T X Y) (T Z W) ⟶ T (T X Z) (T Y W) :=
  (α X Y (T Z W)).hom ≫ L X (swapLeading Seed Y Z W) ≫ (α X Z (T Y W)).inv

private theorem shuffle_natural {X A Y B Z C W D : Q}
    {f : X ⟶ A} (g : Y ⟶ B) {h : Z ⟶ C} {i : W ⟶ D}
    (hf : Centr f) (hh : Centr h) (hi : Centr i) :
    ((f ⊗ₛ g) ⊗ₛ (h ⊗ₛ i)) ≫ shuffle Seed A B C D =
      shuffle Seed X Y Z W ≫ ((f ⊗ₛ h) ⊗ₛ (g ⊗ₛ i)) := by
  unfold shuffle
  rw [← Category.assoc ((f ⊗ₛ g) ⊗ₛ (h ⊗ₛ i)), assoc_tensor, Category.assoc,
    ← Category.assoc (f ⊗ₛ (g ⊗ₛ (h ⊗ₛ i))), tensor_whiskerLeft,
    swapLeading_natural Seed g hh hi, ← whiskerLeft_tensor Seed _ _ hf,
    Category.assoc, unassoc_tensor]
  simp only [Category.assoc]

private theorem map_tensor {X A Y B : Paper.TypeCategory (τ := τ) Φ}
    (f : X ⟶ A) (g : Y ⟶ B) :
    (proj).map (Paper.TypeCategory.tensorSequence f g) = (proj).map f ⊗ₛ (proj).map g := by
  rw [Paper.TypeCategory.tensorSequence, Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
private theorem diagonal_shuffle (A B : τ) :
    (δ (Obj A) ⊗ₛ δ (Obj B)) ≫ shuffle Seed (Obj A) (Obj A) (Obj B) (Obj B) =
      δ (Obj (A ×ₜ B)) := by
  have h := congrArg (proj).map (Paper.TypeCategory.diagonal_tensorSequence (Φ := Φ) A B)
  rw [Functor.map_comp, map_tensor, Paper.TypeCategory.middleFour_factorization] at h
  simp only [Functor.map_comp] at h
  rw [← whiskerLeft_map] at h
  simp only [Functor.map_comp] at h
  rw [← whiskerRight_map] at h
  -- The remaining conversions are the explicitly chosen structure isomorphisms.
  have a₁ : (proj).map (Paper.TypeCategory.associate A A (B ×ₜ B)) =
      (α (Obj A) (Obj A) (Obj (B ×ₜ B))).hom := rfl
  have a₂ : (proj).map (Paper.TypeCategory.unassociate A B (A ×ₜ B)) =
      (α (Obj A) (Obj B) (Obj (A ×ₜ B))).inv := rfl
  have a₃ : (proj).map (Paper.TypeCategory.unassociate A B B) =
      (α (Obj A) (Obj B) (Obj B)).inv := rfl
  have a₄ : (proj).map (Paper.TypeCategory.associate B A B) =
      (α (Obj B) (Obj A) (Obj B)).hom := rfl
  have b : (proj).map (Paper.TypeCategory.braid A B) = (β (Obj A) (Obj B)).hom := rfl
  rw [a₁, a₂, a₃, a₄, b] at h
  simp only [shuffle, swapLeading, lc, Category.assoc]
  simp only [Category.assoc] at h
  exact h

private theorem diagonal_copies (A : τ) : CentralCopies Seed (δ (Obj A)) :=
  map_centralCopies Seed ⟨
    Paper.TypeCategory.whiskerCentral_ofRegion_branchValue (.pair (.var rfl) (.var rfl)),
    Paper.TypeCategory.pairArrows_copy_branchValue (.pair (.var rfl) (.var rfl))⟩

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_copies {X A Y B : τ} {f : Obj X ⟶ Obj A} {g : Obj Y ⟶ Obj B}
    (hf : CentralCopies Seed f) (hg : CentralCopies Seed g) :
    pair (f ⊗ₛ g) (f ⊗ₛ g) = (f ⊗ₛ g) ≫ δ (Obj (A ×ₜ B)) := by
  have df : δ (Obj X) ≫ (f ⊗ₛ f) = f ≫ δ (Obj A) := hf.2
  have dg : δ (Obj Y) ≫ (g ⊗ₛ g) = g ≫ δ (Obj B) := hg.2
  change δ (Obj (X ×ₜ Y)) ≫ ((f ⊗ₛ g) ⊗ₛ (f ⊗ₛ g)) = _
  calc
    _ = (δ (Obj X) ⊗ₛ δ (Obj Y)) ≫
        (shuffle Seed (Obj X) (Obj X) (Obj Y) (Obj Y) ≫ ((f ⊗ₛ g) ⊗ₛ (f ⊗ₛ g))) := by
      rw [← diagonal_shuffle Seed X Y, Category.assoc]
      rfl
    _ = ((δ (Obj X) ⊗ₛ δ (Obj Y)) ≫ ((f ⊗ₛ f) ⊗ₛ (g ⊗ₛ g))) ≫
        shuffle Seed (Obj A) (Obj A) (Obj B) (Obj B) := by
      have hn := shuffle_natural Seed f hf.1 hg.1 hg.1
      exact (congrArg (fun k => (δ (Obj X) ⊗ₛ δ (Obj Y)) ≫ k) hn.symm).trans
        (Category.assoc (δ (Obj X) ⊗ₛ δ (Obj Y)) _ _).symm
    _ = _ := by
      rw [← tc Seed _ _ _ _ ((diagonal_copies Seed Y).1 (f ⊗ₛ f)).2,
        df, dg, tc Seed _ _ _ _ (hg.1 (δ (Obj A))).2, Category.assoc, diagonal_shuffle]


private theorem central_of_left {A B : Q} {f : A ⟶ B}
    (hf : ∀ {X Y : Q} (g : X ⟶ Y), R f X ≫ L B g = L A g ≫ R f Y) :
    Centr f := by
  intro X Y g
  refine ⟨hf g, ?_⟩
  apply (cancel_mono (β Y B).hom).1
  simp only [Category.assoc]
  rw [braid_naturality_left Seed, ← Category.assoc (L X f), braid_naturality_right Seed,
    Category.assoc, hf g, braid_naturality_right Seed, ← Category.assoc (R g A),
    braid_naturality_left Seed, Category.assoc]

private theorem left_central (X : Q) {A B : Q} {f : A ⟶ B} (hf : Centr f) :
    Centr (L X f) := by
  apply central_of_left Seed
  intro Y Z g
  apply (cancel_mono (α X B Z).hom).1
  simp only [Category.assoc]
  rw [associate_naturality_right Seed, ← Category.assoc (R (L X f) Y),
    associate_naturality_middle Seed, Category.assoc, ← lc, (hf g).1, lc,
    associate_naturality_middle Seed, ← Category.assoc (L (T X A) g),
    associate_naturality_right Seed, Category.assoc]

private theorem right_central (X : Q) {A B : Q} {f : A ⟶ B} (hf : Centr f) :
    Centr (R f X) := by
  apply central_of_left Seed
  intro Y Z g
  apply (cancel_mono (α B X Z).hom).1
  simp only [Category.assoc]
  rw [associate_naturality_right Seed, ← Category.assoc (R (R f X) Y),
    associate_naturality_left Seed, Category.assoc, (hf (L X g)).1,
    associate_naturality_left Seed, ← Category.assoc (L (T A X) g),
    associate_naturality_right Seed, Category.assoc]

private theorem central_comp {A B C : Q} {f : A ⟶ B} {g : B ⟶ C}
    (hf : Centr f) (hg : Centr g) : Centr (f ≫ g) := by
  apply central_of_left Seed
  intro X Y h
  simp only [rc, Category.assoc, (hg h).1]
  rw [← Category.assoc, (hf h).1, Category.assoc]

private theorem t_central {X A Y B : Q} {f : X ⟶ A} {g : Y ⟶ B}
    (hf : Centr f) (hg : Centr g) : Centr (f ⊗ₛ g) :=
  central_comp Seed (right_central Seed Y hf) (left_central Seed A hg)

theorem pair_mem {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : H f) (hg : H g) : H (pair f g) := by
  have hc := diagonal_copies Seed X
  have hfg := tensor_copies Seed hf.1 hg.1
  refine ⟨⟨central_comp Seed hc.1 (t_central Seed hf.1.1 hg.1.1), ?_⟩, ?_⟩
  · change pair (δ (Obj X) ≫ (f ⊗ₛ g)) (δ (Obj X) ≫ (f ⊗ₛ g)) =
      (δ (Obj X) ≫ (f ⊗ₛ g)) ≫ δ (Obj (A ×ₜ B))
    rw [pair_comp Seed _ _ _ hc, hfg]
    exact (Category.assoc _ _ _).symm
  · change pair f g ≫ d (A ×ₜ B) = d X
    rw [← fst_discard Seed A B, ← Category.assoc, pairing_fst_of_discard Seed f g hg.2]
    exact hf.2

private theorem projections_pair (A B : τ) :
    pair (productFst Seed A B) (productSnd Seed A B) = 𝟙 (Obj (A ×ₜ B)) := by
  rw [← map_pairArrows, Paper.TypeCategory.pairArrows_projections]
  exact (proj).map_id (Paper.TypeCategory.ofType (A ×ₜ B))

theorem reconstruct {X A B : τ} {f : Obj X ⟶ Obj (A ×ₜ B)} (hf : H f) :
    pair (f ≫ productFst Seed A B) (f ≫ productSnd Seed A B) = f := by
  rw [pair_comp Seed _ _ _ hf.1, projections_pair, Category.comp_id]

noncomputable def productIsLimit (A B : τ) : IsLimit (productFan Seed A B) :=
  BinaryFan.IsLimit.mk _
    (fun f g => ⟨pair f.hom g.hom, pair_mem Seed f.property g.property⟩)
    (fun f g => (incl).map_injective (pairing_fst_of_discard Seed f.hom g.hom g.property.2))
    (fun f g => (incl).map_injective (pairing_snd_of_discard Seed f.hom g.hom f.property.2))
    (fun f g p hl hr => (incl).map_injective (by
      have h₁ : p.hom ≫ productFst Seed A B = f.hom := congrArg (incl).map hl
      have h₂ : p.hom ≫ productSnd Seed A B = g.hom := congrArg (incl).map hr
      change p.hom = pair f.hom g.hom
      rw [← h₁, ← h₂, reconstruct Seed p.property]))

section ChosenUnit

variable (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {K : LCtx τ},
  Paper.WithUnitEta.Step Γ r s K → Seed Γ r s K)

include includeUnit in
private theorem unit_discard : d U = 𝟙 (Obj U) := unit_eta_of_include Seed includeUnit

private theorem discard_mem (A : τ) : H (d A) :=
  branch_mem Seed (.unit : Tm.BranchValue [A] (Tm.unit : Tm Φ) U)

noncomputable def unitIsTerminal : IsTerminal (⟨Obj U⟩ : Val) :=
  IsTerminal.ofUniqueHom
    (fun X => ⟨d X.obj.as, discard_mem Seed _⟩)
    (fun _ f => (incl).map_injective (by
      have h := f.property.2
      change f.hom ≫ d U = _ at h
      rw [unit_discard Seed includeUnit, Category.comp_id] at h
      exact h))

private theorem whiskerLeft_pair (X : τ) {A B : τ} (f : Obj A ⟶ Obj B) :
    L (Obj X) f = pair (productFst Seed X A) (productSnd Seed X A ≫ f) := by
  calc
    _ = pair (productFst Seed X A) (productSnd Seed X A) ≫ L (Obj X) f := by
      rw [projections_pair, Category.id_comp]
    _ = _ := by simp only [pairArrows, lc, Category.assoc]

private theorem whiskerRight_pair (X : τ) {A B : τ} {f : Obj A ⟶ Obj B} (hf : H f) :
    R f (Obj X) = pair (productFst Seed A X ≫ f) (productSnd Seed A X) := by
  calc
    _ = pair (productFst Seed A X) (productSnd Seed A X) ≫ R f (Obj X) := by
      rw [projections_pair, Category.id_comp]
    _ = _ := by
      simp only [pairArrows, rc, Category.assoc]
      rw [(hf.1.1 (productSnd Seed A X)).1]

end ChosenUnit

open scoped MonoidalCategory

theorem map_whiskerLeft
    (unitLimit : IsTerminal (⟨Obj U⟩ : Val))
    (binaryLimit : ∀ (A B : τ), IsLimit (productFan Seed A B))
    (X : τ) {A B : τ}
    (f : (⟨Obj A⟩ : Val) ⟶ ⟨Obj B⟩) :
    letI := cartesianOfLimits Seed unitLimit binaryLimit
    (incl).map ((⟨Obj X⟩ : Val) ◁ f) = L (Obj X) f.hom := by
  let := cartesianOfLimits Seed unitLimit binaryLimit
  rw [whiskerLeft_pair]
  have h := pair_mem Seed (fst_mem Seed X A)
    ((H).comp_mem _ _ (snd_mem Seed X A) f.property)
  let g : (⟨Obj (X ×ₜ A)⟩ : Val) ⟶ ⟨Obj (X ×ₜ B)⟩ := ⟨_, h⟩
  have e : (⟨Obj X⟩ : Val) ◁ f = g :=
    CartesianMonoidalCategory.hom_ext ((⟨Obj X⟩ : Val) ◁ f) g ?_ ?_
  · exact congrArg (incl).map e
  · rw [CartesianMonoidalCategory.whiskerLeft_fst]
    apply (incl).map_injective
    exact (pairing_fst_of_discard Seed _ _
      ((H).comp_mem _ _ (snd_mem Seed X A) f.property).2).symm
  · rw [CartesianMonoidalCategory.whiskerLeft_snd]
    apply (incl).map_injective
    exact (pairing_snd_of_discard Seed _ _ (fst_mem Seed X A).2).symm

theorem map_whiskerRight
    (unitLimit : IsTerminal (⟨Obj U⟩ : Val))
    (binaryLimit : ∀ (A B : τ), IsLimit (productFan Seed A B))
    (X : τ) {A B : τ}
    (f : (⟨Obj A⟩ : Val) ⟶ ⟨Obj B⟩) :
    letI := cartesianOfLimits Seed unitLimit binaryLimit
    (incl).map (f ▷ (⟨Obj X⟩ : Val)) = R f.hom (Obj X) := by
  let := cartesianOfLimits Seed unitLimit binaryLimit
  rw [whiskerRight_pair Seed X f.property]
  have h := pair_mem Seed ((H).comp_mem _ _ (fst_mem Seed A X) f.property) (snd_mem Seed A X)
  let g : (⟨Obj (A ×ₜ X)⟩ : Val) ⟶ ⟨Obj (B ×ₜ X)⟩ := ⟨_, h⟩
  have e : f ▷ (⟨Obj X⟩ : Val) = g :=
    CartesianMonoidalCategory.hom_ext (f ▷ (⟨Obj X⟩ : Val)) g ?_ ?_
  · exact congrArg (incl).map e
  · rw [CartesianMonoidalCategory.whiskerRight_fst]
    apply (incl).map_injective
    exact (pairing_fst_of_discard Seed _ _ (snd_mem Seed A X).2).symm
  · rw [CartesianMonoidalCategory.whiskerRight_snd]
    apply (incl).map_injective
    exact (pairing_snd_of_discard Seed _ _
      ((H).comp_mem _ _ (fst_mem Seed A X) f.property).2).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValueProducts
