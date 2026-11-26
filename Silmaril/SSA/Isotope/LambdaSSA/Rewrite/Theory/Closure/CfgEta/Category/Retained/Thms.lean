module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Retained.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Retained

/-! # Retained-context let and case transport -/

public section

open Silmaril
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open CfgEta CfgEta.TypeCategory CfgEta.TypeCategory.ConstructorReification
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend duplicate retainLeft bind caseWithContext splitMapCoprod)

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.Retained

section PackedCase

variable {τ : Type u} [TypeFormers τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel τ V)
  {X A B D : τ}

variable [DistributiveTensor V] in
theorem packedDistributor_inl (X A B : τ) :
    (M.productIso X A).hom ≫ (M.obj X ◁ inlMap M A B) ≫
      (M.productIso X (Silmaril.coprod A B)).inv ≫ packedDistributor M X A B =
    inlMap M (Silmaril.product X A) (Silmaril.product X B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Retained.packedDistributor_inl M X A B

variable [DistributiveTensor V] in
theorem packedDistributor_inr (X A B : τ) :
    (M.productIso X B).hom ≫ (M.obj X ◁ inrMap M A B) ≫
      (M.productIso X (Silmaril.coprod A B)).inv ≫ packedDistributor M X A B =
    inrMap M (Silmaril.product X A) (Silmaril.product X B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Retained.packedDistributor_inr M X A B

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]


/-- After retaining the input of a case, all that remains is the pure
distributor and the coproduct of the two packed arms. -/
theorem case_factor
    (f : J.obj (M.obj X) ⟶ J.obj (M.obj (Silmaril.coprod A B)))
    (g : J.obj (M.obj (Silmaril.product X A)) ⟶ J.obj (M.obj D))
    (h : J.obj (M.obj (Silmaril.product X B)) ⟶ J.obj (M.obj D)) :
    caseWithContext J (f ≫ J.map (M.coprodIso A B).hom)
      (J.map (M.productIso X A).inv ≫ g) (J.map (M.productIso X B).inv ≫ h) =
    (extend J f ≫ J.map (M.productIso X (Silmaril.coprod A B)).inv) ≫
      J.map (packedDistributor M X A B) ≫ packedCopair J M g h :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Retained.case_factor
    M J f g h

end PackedCase

section Syntactic

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (J : V ⥤ TypeCategory Φ ([] : VCtx τ)) (M : TypeModel τ V)
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) (Γ := []) A)
  {X A B D : τ}

theorem transportHom_comp (f : J.obj (M.obj X) ⟶ J.obj (M.obj A))
    (g : J.obj (M.obj A) ⟶ J.obj (M.obj B)) :
    transportHom J M objIso (f ≫ g) = transportHom J M objIso f ≫ transportHom J M objIso g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Retained.transportHom_comp
    J M objIso f g

section Freyd

variable [SymmetricCategory V] [PremonoidalCategory (TypeCategory Φ ([] : VCtx τ))]
  [SymmetricPremonoidalCategory (TypeCategory Φ ([] : VCtx τ))] [FreydCategory J]

/-- Context extension is transported by agreement on the diagonal and one left whisker. -/
theorem extend_transport (f : J.obj (M.obj X) ⟶ J.obj (M.obj A))
    (hCopy : mapTypeHom J M objIso (duplicate (M.obj X) ≫ (M.productIso X X).inv) = duplicateArrow X)
    (hWhisker : transportHom J M objIso
      (J.map (M.productIso X X).hom ≫ retainLeft J (R := M.obj X) f ≫
        J.map (M.productIso X A).inv) = whiskerLeft (ofType X) (transportHom J M objIso f)) :
    transportHom J M objIso (extend J f ≫ J.map (M.productIso X A).inv) =
      duplicateArrow X ≫ whiskerLeft (ofType X) (transportHom J M objIso f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Retained.extend_transport
    J M objIso f hCopy hWhisker

/-- Transport a retained-context bind and reassemble the actual syntactic
composition of copy, left whiskering and the body on its packed input. -/
theorem bind_transport {p q : Region Φ}
    (hp : ValueBranches [X] p [A]) (hq : ValueBranches [Silmaril.product X A] q [B])
    (f : J.obj (M.obj X) ⟶ J.obj (M.obj A))
    (g : J.obj (M.obj (Silmaril.product X A)) ⟶ J.obj (M.obj B))
    (hf : transportHom J M objIso f = ofRegion hp) (hg : transportHom J M objIso g = ofRegion hq)
    (hCopy : mapTypeHom J M objIso (duplicate (M.obj X) ≫ (M.productIso X X).inv) = duplicateArrow X)
    (hWhisker : transportHom J M objIso
      (J.map (M.productIso X X).hom ≫ retainLeft J (R := M.obj X) f ≫
        J.map (M.productIso X A).inv) = whiskerLeft (ofType X) (transportHom J M objIso f)) :
    transportHom J M objIso (bind J f (J.map (M.productIso X A).inv ≫ g)) =
      ofRegion (seqValueBranches (seqValueBranches
        (duplicateBranches X)
        (whiskerLeftRegion_typed X hp)) hq) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Retained.bind_transport
    J M objIso hp hq f g hf hg hCopy hWhisker

end Freyd

section Distributive

variable [SymmetricCategory V] [PremonoidalCategory (TypeCategory Φ ([] : VCtx τ))]
  [SymmetricPremonoidalCategory (TypeCategory Φ ([] : VCtx τ))]
  [HasFiniteCoproducts (TypeCategory Φ ([] : VCtx τ))]
  [DistributiveTensor V] [DistributivePremonoidalCategory (TypeCategory Φ ([] : VCtx τ))]
  [DistributiveFreydCategory J]

theorem packedCopair_transport {r s : Region Φ}
    (hr : ValueBranches [A] r [D]) (hs : ValueBranches [B] s [D])
    (f : J.obj (M.obj A) ⟶ J.obj (M.obj D)) (g : J.obj (M.obj B) ⟶ J.obj (M.obj D))
    (hf : transportHom J M objIso f = ofRegion hr) (hg : transportHom J M objIso g = ofRegion hs)
    (hInl : mapTypeHom J M objIso (inlMap M A B) = (sumCofan (Φ := Φ) (Γ := []) A B).inl)
    (hInr : mapTypeHom J M objIso (inrMap M A B) = (sumCofan (Φ := Φ) (Γ := []) A B).inr) :
    transportHom J M objIso (packedCopair J M f g) = ofRegion (caseValueBranches hr hs) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Retained.packedCopair_transport
    J M objIso hr hs f g hf hg hInl hInr

/-- Transport a retained-context case using the diagonal, left whisker,
sum injections, and the distributor on the packed types. -/
theorem case_transport {p r s : Region Φ}
    (hp : ValueBranches [X] p [Silmaril.coprod A B])
    (hr : ValueBranches [Silmaril.product X A] r [D])
    (hs : ValueBranches [Silmaril.product X B] s [D])
    (f : J.obj (M.obj X) ⟶ J.obj (M.obj (Silmaril.coprod A B)))
    (g : J.obj (M.obj (Silmaril.product X A)) ⟶ J.obj (M.obj D))
    (h : J.obj (M.obj (Silmaril.product X B)) ⟶ J.obj (M.obj D))
    (hf : transportHom J M objIso f = ofRegion hp)
    (hg : transportHom J M objIso g = ofRegion hr)
    (hh : transportHom J M objIso h = ofRegion hs)
    (hInl : mapTypeHom J M objIso
      (inlMap M (Silmaril.product X A) (Silmaril.product X B)) =
      (sumCofan (Φ := Φ) (Γ := []) (Silmaril.product X A) (Silmaril.product X B)).inl)
    (hInr : mapTypeHom J M objIso
      (inrMap M (Silmaril.product X A) (Silmaril.product X B)) =
      (sumCofan (Φ := Φ) (Γ := []) (Silmaril.product X A) (Silmaril.product X B)).inr)
    (hCopy : mapTypeHom J M objIso (duplicate (M.obj X) ≫ (M.productIso X X).inv) = duplicateArrow X)
    (hWhisker : transportHom J M objIso
      (J.map (M.productIso X X).hom ≫ retainLeft J (R := M.obj X) f ≫
        J.map (M.productIso X (Silmaril.coprod A B)).inv) =
      whiskerLeft (ofType X) (transportHom J M objIso f))
    (hDistrib : transportHom J M objIso (J.map (packedDistributor M X A B)) =
      ofRegion (distributorRegion_typed X A B)) :
    transportHom J M objIso (caseWithContext J (f ≫ J.map (M.coprodIso A B).hom)
      (J.map (M.productIso X A).inv ≫ g) (J.map (M.productIso X B).inv ≫ h)) =
      ofRegion (seqValueBranches (seqValueBranches (seqValueBranches (duplicateBranches X)
        (whiskerLeftRegion_typed X hp)) (distributorRegion_typed X A B))
        (caseValueBranches hr hs)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Retained.case_transport
    J M objIso hp hr hs f g h hf hg hh hInl hInr hCopy hWhisker hDistrib

end Distributive

end Syntactic

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.Retained
