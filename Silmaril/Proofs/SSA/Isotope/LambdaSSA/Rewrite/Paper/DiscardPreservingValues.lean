module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # Terminality and product proofs for discard-preserving values -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingValues

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "U" => (Silmaril.unit : τ)

set_option hygiene false in
local notation "Values" => DiscardPreservingValueCategory Seed pe

set_option backward.isDefEq.respectTransparency false in
private theorem discard_id
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L) :
    discardArrow Seed U = 𝟙 (Obj U) := by
  rw [← (projection Seed).map_id, ← Paper.TypeCategory.ofRegion_id]
  exact (ofRegion_eq_iff Seed _ _).2 (.extra (.br rfl .unit) (.br rfl (.var rfl)) (includeUnit .unit))

set_option backward.isDefEq.respectTransparency false in
noncomputable def discardPreservingUnitIsTerminal
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L) :
    IsTerminal (⟨Obj U⟩ : Values) := by
  have h := discard_id Seed includeUnit
  let drop (X : Values) : X ⟶ ⟨Obj U⟩ := by
    let T : τ := X.obj.as
    have hu : Tm.BranchValue [T] (Tm.unit : Tm Φ) U := .unit
    exact ⟨discardArrow Seed T, projected_branchValue_mem Seed pe hu,
      (congrArg (_ ≫ ·) h).trans (Category.comp_id _)⟩
  refine IsTerminal.ofUniqueHom drop ?_
  intro X f
  apply WideSubcategory.hom_ext
  exact (Category.comp_id f.1).symm.trans ((congrArg (f.1 ≫ ·) h).symm.trans f.2.2)

variable (includeProjection : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
  Paper.WithProjectionReturns.Step Γ r s L → Seed Γ r s L)

set_option backward.isDefEq.respectTransparency false in
noncomputable def discardPreservingFanIsLimit (A B : τ)
    (close : ∀ {X : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B},
      DiscardPreservingReturn Seed pe f → DiscardPreservingReturn Seed pe g →
      ∃ p : Paper.TypeCategory.ofType (Φ := Φ) X ⟶ Paper.TypeCategory.ofType (product A B),
        Paper.TypeCategory.CentralCopies p ∧ (projection Seed).map p = pairArrows Seed f g) :
    IsLimit (discardPreservingFan Seed pe includeProjection A B) := by
  let pair {X : Values} (f : X ⟶ ⟨Obj A⟩) (g : X ⟶ ⟨Obj B⟩) :
      X ⟶ (discardPreservingFan Seed pe includeProjection A B).pt := by
    have hf := pairing_fst_of_discard Seed f.1 g.1 g.2.2
    refine ⟨pairArrows Seed f.1 g.1,
      ⟨projectedPureReturn_pairArrows Seed pe f.2.1.1 g.2.1.1, close f.2 g.2⟩, ?_⟩
    change pairArrows Seed f.1 g.1 ≫ discardArrow Seed (product A B) = discardArrow Seed X.obj.as
    rw [← fst_discard Seed A B, ← Category.assoc, hf]
    exact f.2.2
  refine BinaryFan.IsLimit.mk _ (@pair) ?_ ?_ ?_
  · intro X f g
    apply WideSubcategory.hom_ext
    change pairArrows Seed f.1 g.1 ≫ productFst Seed A B = f.1
    exact pairing_fst_of_discard Seed f.1 g.1 g.2.2
  · intro X f g
    apply WideSubcategory.hom_ext
    change pairArrows Seed f.1 g.1 ≫ productSnd Seed A B = g.1
    exact pairing_snd_of_discard Seed f.1 g.1 f.2.2
  · intro X f g p hl hr
    apply WideSubcategory.hom_ext
    have hl' : p.1 ≫ productFst Seed A B = f.1 := congrArg (·.1) hl
    have hr' : p.1 ≫ productSnd Seed A B = g.1 := congrArg (·.1) hr
    exact projections_ext Seed pe p.2.1 (pair f g).2.1
      (hl'.trans (pairing_fst_of_discard Seed f.1 g.1 g.2.2).symm)
      (hr'.trans (pairing_snd_of_discard Seed f.1 g.1 f.2.2).symm)

set_option backward.isDefEq.respectTransparency false in
noncomputable def discardPreservingRightUnitIsLimit (A : τ)
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L) :
    IsLimit (discardPreservingFan Seed pe includeProjection A U) := by
  apply discardPreservingFanIsLimit Seed pe includeProjection A U
  intro X f g hf hg
  have hi := discard_id Seed includeUnit
  have hg' : g = discardArrow Seed X := by
    have hd : g ≫ discardArrow Seed U = discardArrow Seed X := hg.2
    rwa [hi, Category.comp_id] at hd
  have hf' : f ≫ discardArrow Seed A = discardArrow Seed X := hf.2
  let a : Tm.BranchValue [A] (.var 0 : Tm Φ) A := .var rfl
  let u : Tm.BranchValue [A] (.unit : Tm Φ) U := .unit
  let append := Paper.TypeCategory.ofRegion (.br (ℓ := 0) rfl (.pair a u))
  obtain ⟨f₀, hf₀, hfmap⟩ := hf.1.2
  have : Paper.TypeCategory.CentralCopies append :=
    ⟨Paper.TypeCategory.whiskerCentral_ofRegion_branchValue (.pair a u),
      Paper.TypeCategory.pairArrows_copy_branchValue (.pair a u)⟩
  have ha : (projection Seed).map append =
      pairArrows Seed (𝟙 (Obj A)) (discardArrow Seed A) := by
    rw [← (projection Seed).map_id, ← map_pairArrows, ← Paper.TypeCategory.ofRegion_id]
    exact congrArg (projection Seed).map (Paper.TypeCategory.pairArrows_branchValue a u).symm
  refine ⟨f₀ ≫ append,
    ⟨Paper.TypeCategory.WhiskerCentral.comp hf₀.1 this.1,
      Paper.TypeCategory.pairArrows_copy_comp (τ := τ) f₀ append hf₀.1 hf₀.2 this.2⟩, ?_⟩
  rw [(projection Seed).map_comp, hfmap, hg', ← hf', ha]
  have d := (hf.1.centralCopies).2
  change pairArrows Seed f f = f ≫ diagonalArrow Seed (Obj A) at d
  have L (h : Obj X ⟶ Obj A) (k : Obj A ⟶ Obj U) :
      whiskerLeft Seed (Obj A) (h ≫ k) =
        whiskerLeft Seed (Obj A) h ≫ whiskerLeft Seed (Obj A) k :=
    (whiskerLeftFunctor Seed (Obj A)).map_comp h k
  have R : whiskerRight Seed (𝟙 (Obj A)) (Obj A) = 𝟙 _ :=
    (whiskerRightFunctor Seed (Obj A)).map_id _
  calc
    _ = (f ≫ diagonalArrow Seed (Obj A)) ≫ whiskerLeft Seed (Obj A) (discardArrow Seed A) := by
      unfold pairArrows
      rw [R, Category.id_comp, Category.assoc]
    _ = pairArrows Seed f f ≫ whiskerLeft Seed (Obj A) (discardArrow Seed A) := by rw [d]
    _ = _ := by
      unfold pairArrows
      simp only [L, Category.assoc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingValues
