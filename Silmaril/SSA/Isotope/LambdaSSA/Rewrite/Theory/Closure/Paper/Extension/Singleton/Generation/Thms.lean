module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonGeneration

/-! # Uniqueness on the generated contextual singleton category -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Generation

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open Paper.Extension.Singleton (TypeCategory)
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (ofType sumCofan sumIso whiskerLeftFunctor whiskerRightFunctor
  iterateSum discardArrow productFst productSnd pairArrows diagonalArrow sumCofanIsColimit ofRegion)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open scoped MonoidalCategory

universe u v w x

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
set_option hygiene false in
local notation "Obj" => ofType (Seed)

section Target

variable {C : Type w} [Category.{x} C] [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C]
  {X : τ → C}

variable (F : TypeCategory Seed ⥤ C) (objIso : ∀ A : τ, F.obj (Obj A) ≅ X A)

omit [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C] in
@[simp] theorem mapInCoordinates_id (A : τ) :
    mapInCoordinates Seed F objIso (𝟙 (Obj A)) = 𝟙 (X A) :=
  SingletonGeneration.mapInCoordinates_id Seed F objIso A

omit [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C] in
theorem mapInCoordinates_comp {A B D : τ} (f : Obj A ⟶ Obj B) (g : Obj B ⟶ Obj D) :
    mapInCoordinates Seed F objIso (f ≫ g) =
      mapInCoordinates Seed F objIso f ≫ mapInCoordinates Seed F objIso g :=
  SingletonGeneration.mapInCoordinates_comp Seed F objIso f g

/-- Preservation of the two injections determines the image of the exact copair. -/
theorem mapInCoordinates_exactCopair (T : Coordinates X) (h : Preserves Seed F objIso T)
    {A B D : τ} (f : Obj A ⟶ Obj D) (g : Obj B ⟶ Obj D) :
    mapInCoordinates Seed F objIso (exactCopair (Seed) f g) =
      (T.sumIso A B).hom ≫
        CategoryTheory.Limits.coprod.desc (mapInCoordinates Seed F objIso f) (mapInCoordinates Seed F objIso g) :=
  SingletonGeneration.mapInCoordinates_exactCopair Seed F objIso T h f g

variable (G : TypeCategory Seed ⥤ C) (otherIso : ∀ A : τ, G.obj (Obj A) ≅ X A)

/-- Comparison functors preserving the stated structure and agreeing on each
typed primitive agree on every generated computation. -/
theorem mapInCoordinates_eq_of_generated (T : Coordinates X)
    (hF : Preserves Seed F objIso T) (hG : Preserves Seed G otherIso T)
    (hp : ∀ p : Φ, mapInCoordinates Seed F objIso (primitive Seed p) = mapInCoordinates Seed G otherIso (primitive Seed p))
    {A B : τ} {f : Obj A ⟶ Obj B} (hf : Generated Seed f) :
    mapInCoordinates Seed F objIso f = mapInCoordinates Seed G otherIso f :=
  SingletonGeneration.mapInCoordinates_eq_of_generated Seed F objIso G otherIso T hF hG hp hf

/-- The two designated type isomorphisms give a naturality square on each generated arrow. -/
theorem naturality_of_generated (T : Coordinates X)
    (hF : Preserves Seed F objIso T) (hG : Preserves Seed G otherIso T)
    (hp : ∀ p : Φ, mapInCoordinates Seed F objIso (primitive Seed p) = mapInCoordinates Seed G otherIso (primitive Seed p))
    {A B : τ} {f : Obj A ⟶ Obj B} (hf : Generated Seed f) :
    F.map f ≫ (objIso B ≪≫ (otherIso B).symm).hom =
      (objIso A ≪≫ (otherIso A).symm).hom ≫ G.map f :=
  SingletonGeneration.naturality_of_generated Seed F objIso G otherIso T hF hG hp hf

/-- The comparisons are naturally isomorphic on the generated wide subcategory, with components
`objIso A ≪≫ (otherIso A).symm` at the exact syntax types. -/
noncomputable def generatedIso (T : Coordinates X)
    (hF : Preserves Seed F objIso T) (hG : Preserves Seed G otherIso T)
    (hp : ∀ p : Φ, mapInCoordinates Seed F objIso (primitive Seed p) = mapInCoordinates Seed G otherIso (primitive Seed p)) :
    generatedInclusion Seed ⋙ F ≅ generatedInclusion Seed ⋙ G :=
  SingletonGeneration.generatedIso Seed F objIso G otherIso T hF hG hp

end Target

open CfgEta.TypeCategory (caseValueBranches returnRegion_typed)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)

local notation "Lit" => ofRegion (Seed)

/-- The coproduct operation has the literal guarded region case as representative. -/
theorem exactCopair_ofRegion {A B D : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [D]) (hs : ValueBranches [B] s [D]) :
    exactCopair (Seed) (Lit hr) (Lit hs) = Lit (caseValueBranches hr hs) :=
  SingletonGeneration.exactCopair_ofRegion Seed hr hs

theorem Generated.caseOnInput {A B D : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [D]) (hs : ValueBranches [B] s [D])
    (gr : Generated Seed (Lit hr)) (gs : Generated Seed (Lit hs)) :
    Generated Seed (Lit (caseValueBranches hr hs)) :=
  SingletonGeneration.Generated.caseOnInput Seed hr hs gr gs

theorem Generated.pair {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : Generated Seed f) (hg : Generated Seed g) : Generated Seed (pairArrows (Seed) f g) :=
  SingletonGeneration.Generated.pair Seed hf hg

/-- The return of every typed constructor value is generated. -/
theorem generated_branchValue {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    Generated Seed (Lit (.br (ℓ := 0) rfl ha)) :=
  SingletonGeneration.generated_branchValue Seed ha

/-- A primitive applied to a constructor value is generated. -/
theorem generated_primitive_branchValue {X : τ} {a : Tm Φ} (p : Φ)
    (ha : Tm.BranchValue [X] a (instrSrc p)) :
    Generated Seed (Lit (returnRegion_typed (.op (f := p) ha.hasType))) :=
  SingletonGeneration.generated_primitive_branchValue Seed p ha

/-- The exact distributor is generated as the inverse of the copair of the two whiskered injections. -/
theorem generated_distributor (X A B : τ) :
    Generated Seed (Lit (distributorRegion_typed X A B)) :=
  SingletonGeneration.generated_distributor Seed X A B

/-- A retained region case is generated from its retagging scrutinee and packed arms. -/
theorem Generated.retainedCase {X A B D : τ} {a : Tm Φ} {l r : Region Φ}
    (ha : Tm.HasType [X] a (coprod A B)) (hl : ValueBranches [A, X] l [D])
    (hr : ValueBranches [B, X] r [D])
    (gs : Generated Seed (Lit (Paper.RetainedCase.returnSum_typed ha)))
    (gl : Generated Seed (Lit (Paper.RetainedLet.unpackBody_typed hl)))
    (gr : Generated Seed (Lit (Paper.RetainedLet.unpackBody_typed hr))) :
    Generated Seed (Lit (.case ha hl hr)) :=
  SingletonGeneration.Generated.retainedCase Seed ha hl hr gs gl gr

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Generation
