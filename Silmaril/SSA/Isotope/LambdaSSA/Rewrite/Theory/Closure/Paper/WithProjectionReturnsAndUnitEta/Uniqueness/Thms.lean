module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Uniqueness.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedSingletonUniqueness

/-! # Uniqueness on the generated joined singleton category -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Uniqueness

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
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
    mapInCoordinates F objIso (𝟙 (Obj A)) = 𝟙 (X A) :=
  JoinedSingletonUniqueness.mapInCoordinates_id F objIso A

omit [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C] in
theorem mapInCoordinates_comp {A B D : τ} (f : Obj A ⟶ Obj B) (g : Obj B ⟶ Obj D) :
    mapInCoordinates F objIso (f ≫ g) =
      mapInCoordinates F objIso f ≫ mapInCoordinates F objIso g :=
  JoinedSingletonUniqueness.mapInCoordinates_comp F objIso f g

/-- Preservation of the two injections determines the image of the exact copair. -/
theorem mapInCoordinates_exactCopair (T : Coordinates X) (h : Preserves F objIso T)
    {A B D : τ} (f : Obj A ⟶ Obj D) (g : Obj B ⟶ Obj D) :
    mapInCoordinates F objIso (exactCopair (Seed) f g) =
      (T.sumIso A B).hom ≫
        CategoryTheory.Limits.coprod.desc (mapInCoordinates F objIso f) (mapInCoordinates F objIso g) :=
  JoinedSingletonUniqueness.mapInCoordinates_exactCopair F objIso T h f g

variable (G : TypeCategory (τ := τ) (Φ := Φ) ⥤ C) (otherIso : ∀ A : τ, G.obj (Obj A) ≅ X A)

/-- Comparison functors preserving the stated structure and agreeing on each
typed primitive agree on every generated computation. -/
theorem mapInCoordinates_eq_of_generated (T : Coordinates X)
    (hF : Preserves F objIso T) (hG : Preserves G otherIso T)
    (hp : ∀ p : Φ, mapInCoordinates F objIso (primitive p) = mapInCoordinates G otherIso (primitive p))
    {A B : τ} {f : Obj A ⟶ Obj B} (hf : Generated f) :
    mapInCoordinates F objIso f = mapInCoordinates G otherIso f :=
  JoinedSingletonUniqueness.mapInCoordinates_eq_of_generated F objIso G otherIso T hF hG hp hf

/-- The two designated type isomorphisms give a naturality square on each generated arrow. -/
theorem naturality_of_generated (T : Coordinates X)
    (hF : Preserves F objIso T) (hG : Preserves G otherIso T)
    (hp : ∀ p : Φ, mapInCoordinates F objIso (primitive p) = mapInCoordinates G otherIso (primitive p))
    {A B : τ} {f : Obj A ⟶ Obj B} (hf : Generated f) :
    F.map f ≫ (objIso B ≪≫ (otherIso B).symm).hom =
      (objIso A ≪≫ (otherIso A).symm).hom ≫ G.map f :=
  JoinedSingletonUniqueness.naturality_of_generated F objIso G otherIso T hF hG hp hf

/-- The comparisons are naturally isomorphic on the generated wide subcategory, with components
`objIso A ≪≫ (otherIso A).symm` at the exact syntax types. -/
noncomputable def generatedIso (T : Coordinates X)
    (hF : Preserves F objIso T) (hG : Preserves G otherIso T)
    (hp : ∀ p : Φ, mapInCoordinates F objIso (primitive p) = mapInCoordinates G otherIso (primitive p)) :
    generatedInclusion ⋙ F ≅ generatedInclusion ⋙ G :=
  JoinedSingletonUniqueness.generatedIso F objIso G otherIso T hF hG hp

end Target

open CfgEta.TypeCategory (caseValueBranches returnRegion_typed)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)

local notation "Lit" => ofRegion (Seed)

/-- The coproduct operation has the literal guarded region case as representative. -/
theorem exactCopair_ofRegion {A B D : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [D]) (hs : ValueBranches [B] s [D]) :
    exactCopair (Seed) (Lit hr) (Lit hs) = Lit (caseValueBranches hr hs) :=
  JoinedSingletonUniqueness.exactCopair_ofRegion hr hs

theorem Generated.caseOnInput {A B D : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [D]) (hs : ValueBranches [B] s [D])
    (gr : Generated (Lit hr)) (gs : Generated (Lit hs)) :
    Generated (Lit (caseValueBranches hr hs)) :=
  JoinedSingletonUniqueness.Generated.caseOnInput hr hs gr gs

theorem Generated.pair {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : Generated f) (hg : Generated g) : Generated (pairArrows (Seed) f g) :=
  JoinedSingletonUniqueness.Generated.pair hf hg

/-- The return of every typed constructor value is generated. -/
theorem generated_branchValue {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    Generated (Lit (.br (ℓ := 0) rfl ha)) :=
  JoinedSingletonUniqueness.generated_branchValue ha

/-- A primitive applied to a constructor value is generated. -/
theorem generated_primitive_branchValue {X : τ} {a : Tm Φ} (p : Φ)
    (ha : Tm.BranchValue [X] a (instrSrc p)) :
    Generated (Lit (returnRegion_typed (.op (f := p) ha.hasType))) :=
  JoinedSingletonUniqueness.generated_primitive_branchValue p ha

/-- The exact distributor is generated as the inverse of the copair of the two whiskered injections. -/
theorem generated_distributor (X A B : τ) :
    Generated (Lit (distributorRegion_typed X A B)) :=
  JoinedSingletonUniqueness.generated_distributor X A B

/-- A retained region case is generated from its retagging scrutinee and packed arms. -/
theorem Generated.retainedCase {X A B D : τ} {a : Tm Φ} {l r : Region Φ}
    (ha : Tm.HasType [X] a (coprod A B)) (hl : ValueBranches [A, X] l [D])
    (hr : ValueBranches [B, X] r [D])
    (gs : Generated (Lit (Paper.RetainedCase.returnSum_typed ha)))
    (gl : Generated (Lit (Paper.RetainedLet.unpackBody_typed hl)))
    (gr : Generated (Lit (Paper.RetainedLet.unpackBody_typed hr))) :
    Generated (Lit (.case ha hl hr)) :=
  JoinedSingletonUniqueness.Generated.retainedCase ha hl hr gs gl gr

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Uniqueness
