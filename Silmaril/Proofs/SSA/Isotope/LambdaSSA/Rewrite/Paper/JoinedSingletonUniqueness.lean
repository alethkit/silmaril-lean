module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Uniqueness.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Product.Thms

/-! # Uniqueness on generated joined singleton computations -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedSingletonUniqueness

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithProjectionReturnsAndUnitEta (Step projection TypeCategory)
open Paper.WithProjectionReturnsAndUnitEta.Uniqueness
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (ofType sumCofan sumIso whiskerLeftFunctor whiskerRightFunctor
  iterateSum discardArrow productFst productSnd pairArrows diagonalArrow sumCofanIsColimit ofRegion)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open scoped MonoidalCategory

universe u v w x

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => ofType (Seed)

section Target

variable {C : Type w} [Category.{x} C] [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C]
  {X : τ → C}

variable (F : TypeCategory (τ := τ) (Φ := Φ) ⥤ C) (objIso : ∀ A : τ, F.obj (Obj A) ≅ X A)

omit [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C] in
@[simp] theorem mapInCoordinates_id (A : τ) :
    mapInCoordinates F objIso (𝟙 (Obj A)) = 𝟙 (X A) := by
  simp [mapInCoordinates]

omit [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C] in
theorem mapInCoordinates_comp {A B D : τ} (f : Obj A ⟶ Obj B) (g : Obj B ⟶ Obj D) :
    mapInCoordinates F objIso (f ≫ g) =
      mapInCoordinates F objIso f ≫ mapInCoordinates F objIso g := by
  simp [mapInCoordinates]

private theorem inl_exactCopair {A B D : τ} (f : Obj A ⟶ Obj D) (g : Obj B ⟶ Obj D) :
    (sumCofan (Seed) A B).inl ≫ exactCopair (Seed) f g = f := by
  exact (sumCofanIsColimit (Seed) A B).fac (BinaryCofan.mk f g) ⟨WalkingPair.left⟩

private theorem inr_exactCopair {A B D : τ} (f : Obj A ⟶ Obj D) (g : Obj B ⟶ Obj D) :
    (sumCofan (Seed) A B).inr ≫ exactCopair (Seed) f g = g := by
  exact (sumCofanIsColimit (Seed) A B).fac (BinaryCofan.mk f g) ⟨WalkingPair.right⟩

set_option backward.isDefEq.respectTransparency false in
theorem mapInCoordinates_exactCopair (T : Coordinates X) (h : Preserves F objIso T)
    {A B D : τ} (f : Obj A ⟶ Obj D) (g : Obj B ⟶ Obj D) :
    mapInCoordinates F objIso (exactCopair (Seed) f g) =
      (T.sumIso A B).hom ≫
        CategoryTheory.Limits.coprod.desc (mapInCoordinates F objIso f) (mapInCoordinates F objIso g) := by
  apply (cancel_epi (T.sumIso A B).inv).mp
  apply coprod.hom_ext
  · rw [← Category.assoc, ← h.inl A B, ← mapInCoordinates_comp, inl_exactCopair]
    simp only [Iso.inv_hom_id_assoc, coprod.inl_desc]
  · rw [← Category.assoc, ← h.inr A B, ← mapInCoordinates_comp, inr_exactCopair]
    simp only [Iso.inv_hom_id_assoc, coprod.inr_desc]

variable (G : TypeCategory (τ := τ) (Φ := Φ) ⥤ C) (otherIso : ∀ A : τ, G.obj (Obj A) ≅ X A)

set_option backward.isDefEq.respectTransparency false in
theorem mapInCoordinates_eq_of_generated (T : Coordinates X)
    (hF : Preserves F objIso T) (hG : Preserves G otherIso T)
    (hp : ∀ p : Φ, mapInCoordinates F objIso (primitive p) = mapInCoordinates G otherIso (primitive p))
    {A B : τ} {f : Obj A ⟶ Obj B} (hf : Generated f) :
    mapInCoordinates F objIso f = mapInCoordinates G otherIso f := by
  induction hf with
  | id A => simp
  | comp _ _ ihf ihg => rw [mapInCoordinates_comp, mapInCoordinates_comp, ihf, ihg]
  | inv i _ ih =>
    have : IsIso (mapInCoordinates G otherIso i.hom) := by
      unfold mapInCoordinates
      infer_instance
    apply (cancel_mono (mapInCoordinates G otherIso i.hom)).mp
    calc
      _ = mapInCoordinates F objIso (i.inv ≫ i.hom) := by rw [mapInCoordinates_comp, ih]
      _ = mapInCoordinates G otherIso (i.inv ≫ i.hom) := by simp
      _ = _ := by rw [mapInCoordinates_comp]
  | discard A => rw [hF.discard, hG.discard]
  | fst A B => rw [hF.fst, hG.fst]
  | snd A B => rw [hF.snd, hG.snd]
  | copy A => rw [hF.copy, hG.copy]
  | primitive p => exact hp p
  | initial f => exact T.initial.hom_ext _ _
  | inl A B => rw [hF.inl, hG.inl]
  | inr A B => rw [hF.inr, hG.inr]
  | copair _ _ ihf ihg => rw [mapInCoordinates_exactCopair F objIso T hF,
      mapInCoordinates_exactCopair G otherIso T hG, ihf, ihg]
  | left Y _ ih => rw [hF.left, hG.left, ih]
  | right Y _ ih => rw [hF.right, hG.right, ih]
  | iterate _ ih => rw [hF.iterate, hG.iterate, ih]

set_option backward.isDefEq.respectTransparency false in
/-- The specified object isomorphisms form a naturality square on every
generated arrow. This gives the coherent comparison of the two functors. -/
theorem naturality_of_generated (T : Coordinates X)
    (hF : Preserves F objIso T) (hG : Preserves G otherIso T)
    (hp : ∀ p : Φ, mapInCoordinates F objIso (primitive p) = mapInCoordinates G otherIso (primitive p))
    {A B : τ} {f : Obj A ⟶ Obj B} (hf : Generated f) :
    F.map f ≫ (objIso B ≪≫ (otherIso B).symm).hom =
      (objIso A ≪≫ (otherIso A).symm).hom ≫ G.map f := by
  have h := mapInCoordinates_eq_of_generated F objIso G otherIso T hF hG hp hf
  have h' := congrArg (fun k => (objIso A).hom ≫ k ≫ (otherIso B).inv) h
  simpa only [mapInCoordinates, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.trans_hom, Iso.symm_hom] using h'

/-- Two comparisons agreeing on the primitives are naturally isomorphic on
the generated subcategory through their designated object comparisons. -/
noncomputable def generatedIso (T : Coordinates X)
    (hF : Preserves F objIso T) (hG : Preserves G otherIso T)
    (hp : ∀ p : Φ, mapInCoordinates F objIso (primitive p) = mapInCoordinates G otherIso (primitive p)) :
    generatedInclusion ⋙ F ≅ generatedInclusion ⋙ G :=
  NatIso.ofComponents
    (fun A => objIso (show τ from A.obj.as) ≪≫ (otherIso (show τ from A.obj.as)).symm)
    (fun {A B} f => naturality_of_generated F objIso G otherIso T hF hG hp
      (A := (show τ from A.obj.as)) (B := (show τ from B.obj.as)) f.property)

end Target

open CfgEta.TypeCategory (caseValueBranches returnRegion_branchValue returnRegion_typed)

local notation "P" => projection (τ := τ) (Φ := Φ)
local notation "Lit" => ofRegion (Seed)

set_option backward.isDefEq.respectTransparency false in
theorem exactCopair_ofRegion {A B D : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [D]) (hs : ValueBranches [B] s [D]) :
    exactCopair (Seed) (Lit hr) (Lit hs) = Lit (caseValueBranches hr hs) := by
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit (Seed) A B)
  · rw [inl_exactCopair]
    exact ((P).map_comp _ _).symm ▸ (congrArg (P).map (Paper.RetainedCase.case_ofRegion_inl hr hs)).symm
  · rw [inr_exactCopair]
    exact ((P).map_comp _ _).symm ▸ (congrArg (P).map (Paper.RetainedCase.case_ofRegion_inr hr hs)).symm

theorem Generated.caseOnInput {A B D : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [D]) (hs : ValueBranches [B] s [D])
    (gr : Generated (Lit hr)) (gs : Generated (Lit hs)) :
    Generated (Lit (caseValueBranches hr hs)) :=
  exactCopair_ofRegion hr hs ▸ Generated.copair gr gs

theorem Generated.pair {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : Generated f) (hg : Generated g) : Generated (pairArrows (Seed) f g) :=
  .comp (.copy X) (.comp (.right X hf) (.left A hg))

set_option backward.isDefEq.respectTransparency false in
theorem generated_branchValue {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    Generated (Lit (.br (ℓ := 0) rfl ha)) := by
  induction a generalizing A <;> cases ha
  case var.var =>
    rename_i i hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      change Generated ((P).map (Paper.TypeCategory.ofRegion (.br (ℓ := 0) rfl (.var rfl))))
      rw [Paper.TypeCategory.ofRegion_id, (P).map_id]
      exact .id X
    | succ i => simp [At] at hi
  case unit => exact .discard X
  case pair.pair a b ih1 ih2 A B ha hb =>
    have eq := (Paper.Extension.Singleton.map_pairArrows (Seed) _ _).symm.trans
      (congrArg (P).map (Paper.TypeCategory.pairArrows_branchValue ha hb))
    change Generated ((P).map (Paper.TypeCategory.ofRegion (.br (ℓ := 0) rfl (.pair ha hb))))
    rw [← eq]
    exact Generated.pair (ih1 ha) (ih2 hb)
  case inl.inl a ih A B ha =>
    have h := Generated.comp (ih ha) (Generated.inl A B)
    rw [show (sumCofan (Seed) A B).inl =
      Lit (.br (ℓ := 0) rfl (.inl (.var rfl))) from
        congrArg (P).map (Paper.TypeCategory.sumCofan_inl A B)] at h
    exact h
  case inr.inr a ih B A ha =>
    have h := Generated.comp (ih ha) (Generated.inr A B)
    rw [show (sumCofan (Seed) A B).inr =
      Lit (.br (ℓ := 0) rfl (.inr (.var rfl))) from
        congrArg (P).map (Paper.TypeCategory.sumCofan_inr A B)] at h
    exact h

set_option backward.isDefEq.respectTransparency false in
theorem generated_primitive_branchValue {X : τ} {a : Tm Φ} (p : Φ)
    (ha : Tm.BranchValue [X] a (instrSrc p)) :
    Generated (Lit (returnRegion_typed (.op (f := p) ha.hasType))) := by
  change Generated ((P).map (Paper.TypeCategory.returnTerm (.op (f := p) ha.hasType)))
  rw [Paper.TypeCategory.returnTerm_op_branchValue p ha, Functor.map_comp]
  have e : (P).map (Paper.TypeCategory.returnTerm ha.hasType) = Lit (.br (ℓ := 0) rfl ha) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff (Seed) (returnRegion_typed ha.hasType)
      (.br (ℓ := 0) rfl ha)).2 (.paper (.cfgEta (.native (.base (returnRegion_branchValue ha)))))
  rw [e]
  exact .comp (generated_branchValue ha) (.primitive p)

open CfgEta.TypeCategory.Retained (distributorRegion_typed)

set_option backward.isDefEq.respectTransparency false in
theorem generated_distributor (X A B : τ) :
    Generated (Lit (distributorRegion_typed X A B)) := by
  let d : Obj (product X (coprod A B)) ≅ Obj (coprod (product X A) (product X B)) :=
    (P).mapIso (Paper.RetainedCase.distributorIso X A B)
  let left : Obj (product X A) ⟶ Obj (product X (coprod A B)) :=
    (whiskerLeftFunctor (Seed) (Obj X)).map (sumCofan (Seed) A B).inl
  let right : Obj (product X B) ⟶ Obj (product X (coprod A B)) :=
    (whiskerLeftFunctor (Seed) (Obj X)).map (sumCofan (Seed) A B).inr
  have hom : d.hom = Lit (distributorRegion_typed X A B) :=
    congrArg (P).map (Paper.RetainedCase.distributorIso_hom X A B)
  have hl : left ≫ d.hom = (sumCofan (Seed) (product X A) (product X B)).inl := by
    rw [hom]
    exact ((P).map_comp _ _).symm.trans
      (congrArg (P).map (Paper.RetainedCase.left_distributor_inl X A B))
  have hr : right ≫ d.hom = (sumCofan (Seed) (product X A) (product X B)).inr := by
    rw [hom]
    exact ((P).map_comp _ _).symm.trans
      (congrArg (P).map (Paper.RetainedCase.left_distributor_inr X A B))
  have hinv : d.inv = exactCopair (Seed) left right := by
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit (Seed) (product X A) (product X B))
    · rw [inl_exactCopair, ← hl, Category.assoc, d.hom_inv_id, Category.comp_id]
    · rw [inr_exactCopair, ← hr, Category.assoc, d.hom_inv_id, Category.comp_id]
  rw [← hom]
  apply Generated.inv d.symm
  change Generated d.inv
  rw [hinv]
  exact .copair (.left X (.inl A B)) (.left X (.inr A B))

set_option backward.isDefEq.respectTransparency false in
theorem Generated.retainedCase {X A B D : τ} {a : Tm Φ} {l r : Region Φ}
    (ha : Tm.HasType [X] a (coprod A B)) (hl : ValueBranches [A, X] l [D])
    (hr : ValueBranches [B, X] r [D])
    (gs : Generated (Lit (Paper.RetainedCase.returnSum_typed ha)))
    (gl : Generated (Lit (Paper.RetainedLet.unpackBody_typed hl)))
    (gr : Generated (Lit (Paper.RetainedLet.unpackBody_typed hr))) :
    Generated (Lit (.case ha hl hr)) := by
  change Generated ((P).map (Paper.TypeCategory.ofRegion (.case ha hl hr)))
  rw [← Paper.RetainedCase.literal_case_ofRegion ha hl hr, Paper.RetainedCase.assembledCaseArrow,
    (P).map_comp, (P).map_comp, (P).map_comp]
  exact .comp (.comp (.comp (.copy X) (.left X gs)) (generated_distributor X A B))
    (Generated.caseOnInput _ _ gl gr)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedSingletonUniqueness
