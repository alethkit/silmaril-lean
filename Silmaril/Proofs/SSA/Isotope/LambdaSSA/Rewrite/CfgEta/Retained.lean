module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Retained.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # Proofs of retained-context LambdaSSA transport -/

public section

open Silmaril
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open CfgEta CfgEta.TypeCategory CfgEta.TypeCategory.ConstructorReification
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel extend_postmap)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend duplicate retainLeft bind caseWithContext splitMapCoprod)

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Retained

open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.Retained

section PackedCase

variable {τ : Type u} [TypeFormers τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel τ V)
  {X A B D : τ}

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]

private theorem copair_map {E F P Q T : V} (p : E ⟶ P) (q : F ⟶ Q)
    (l : J.obj P ⟶ J.obj T) (r : J.obj Q ⟶ J.obj T) :
    J.map (coprod.map p q) ≫ splitMapCoprod J P Q ≫ coprod.desc l r =
      splitMapCoprod J E F ≫ coprod.desc (J.map p ≫ l) (J.map q ≫ r) := by
  apply (cancel_epi (coprodComparison J E F)).1
  apply coprod.hom_ext
  · simp only [inl_coprodComparison_assoc, ← J.map_comp_assoc,
      coprod.inl_map, J.map_comp_assoc, splitMapCoprod, map_inl_inv_coprodComparison_assoc,
      coprod.inl_desc]
  · simp only [inr_coprodComparison_assoc, ← J.map_comp_assoc,
      coprod.inr_map, J.map_comp_assoc, splitMapCoprod, map_inr_inv_coprodComparison_assoc,
      coprod.inr_desc]

set_option backward.isDefEq.respectTransparency false in
/-- After retaining the input of a case, all that remains is the pure
distributor and the coproduct of the two packed arms. -/
theorem case_factor
    (f : J.obj (M.obj X) ⟶ J.obj (M.obj (Silmaril.coprod A B)))
    (g : J.obj (M.obj (Silmaril.product X A)) ⟶ J.obj (M.obj D))
    (h : J.obj (M.obj (Silmaril.product X B)) ⟶ J.obj (M.obj D)) :
    caseWithContext J (f ≫ J.map (M.coprodIso A B).hom)
      (J.map (M.productIso X A).inv ≫ g) (J.map (M.productIso X B).inv ≫ h) =
    (extend J f ≫ J.map (M.productIso X (Silmaril.coprod A B)).inv) ≫
      J.map (packedDistributor M X A B) ≫ packedCopair J M g h := by
  have route :
      (M.productIso X (Silmaril.coprod A B)).inv ≫ packedDistributor M X A B ≫
        (M.coprodIso (Silmaril.product X A) (Silmaril.product X B)).hom =
      (M.obj X ◁ (M.coprodIso A B).hom) ≫
        (DistributiveTensor.leftIso (M.obj X) (M.obj A) (M.obj B)).inv ≫
        coprod.map (M.productIso X A).inv (M.productIso X B).inv := by
    simp only [packedDistributor, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  unfold caseWithContext Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind packedCopair
  rw [extend_postmap J f (M.coprodIso A B).hom]
  simp only [Category.assoc, ← J.map_comp_assoc, route]
  simp only [J.map_comp, Category.assoc, copair_map]

end PackedCase

section Syntactic

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (J : V ⥤ TypeCategory Φ ([] : VCtx τ)) (M : TypeModel τ V)
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) (Γ := []) A)
  {X A B D : τ}

theorem transportHom_comp (f : J.obj (M.obj X) ⟶ J.obj (M.obj A))
    (g : J.obj (M.obj A) ⟶ J.obj (M.obj B)) :
    transportHom J M objIso (f ≫ g) = transportHom J M objIso f ≫ transportHom J M objIso g := by
  simp [transportHom]

section Freyd

variable [SymmetricCategory V] [PremonoidalCategory (TypeCategory Φ ([] : VCtx τ))]
  [SymmetricPremonoidalCategory (TypeCategory Φ ([] : VCtx τ))] [FreydCategory J]

set_option backward.isDefEq.respectTransparency false in
/-- Context extension is transported by agreement on the diagonal and one left whisker. -/
theorem extend_transport (f : J.obj (M.obj X) ⟶ J.obj (M.obj A))
    (hCopy : mapTypeHom J M objIso (duplicate (M.obj X) ≫ (M.productIso X X).inv) = duplicateArrow X)
    (hWhisker : transportHom J M objIso
      (J.map (M.productIso X X).hom ≫ retainLeft J (R := M.obj X) f ≫
        J.map (M.productIso X A).inv) = whiskerLeft (ofType X) (transportHom J M objIso f)) :
    transportHom J M objIso (extend J f ≫ J.map (M.productIso X A).inv) =
      duplicateArrow X ≫ whiskerLeft (ofType X) (transportHom J M objIso f) := by
  rw [← hCopy, ← hWhisker]
  rw [show extend J f = J.map (duplicate (M.obj X)) ≫ retainLeft J f from rfl]
  rw [Category.assoc (J.map (duplicate (M.obj X))) (retainLeft J f)]
  change _ = transportHom J M objIso (J.map (duplicate (M.obj X) ≫ (M.productIso X X).inv)) ≫
    transportHom J M objIso (J.map (M.productIso X X).hom ≫ retainLeft J f ≫ J.map (M.productIso X A).inv)
  rw [← transportHom_comp J M objIso]
  simp only [Category.assoc, ← J.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
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
        (whiskerLeftRegion_typed X hp)) hq) := by
  unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
  rw [← Category.assoc, transportHom_comp, extend_transport J M objIso f hCopy hWhisker, hf, hg,
    whiskerLeft_ofRegion, duplicateArrow, ofRegion_comp, ofRegion_comp]

end Freyd

section Distributive

variable [SymmetricCategory V] [PremonoidalCategory (TypeCategory Φ ([] : VCtx τ))]
  [SymmetricPremonoidalCategory (TypeCategory Φ ([] : VCtx τ))]
  [HasFiniteCoproducts (TypeCategory Φ ([] : VCtx τ))]
  [DistributiveTensor V] [DistributivePremonoidalCategory (TypeCategory Φ ([] : VCtx τ))]
  [DistributiveFreydCategory J]

set_option backward.isDefEq.respectTransparency false in
theorem packedCopair_transport {r s : Region Φ}
    (hr : ValueBranches [A] r [D]) (hs : ValueBranches [B] s [D])
    (f : J.obj (M.obj A) ⟶ J.obj (M.obj D)) (g : J.obj (M.obj B) ⟶ J.obj (M.obj D))
    (hf : transportHom J M objIso f = ofRegion hr) (hg : transportHom J M objIso g = ofRegion hs)
    (hInl : mapTypeHom J M objIso (inlMap M A B) = (sumCofan (Φ := Φ) (Γ := []) A B).inl)
    (hInr : mapTypeHom J M objIso (inrMap M A B) = (sumCofan (Φ := Φ) (Γ := []) A B).inr) :
    transportHom J M objIso (packedCopair J M f g) = ofRegion (caseValueBranches hr hs) := by
  rw [← coprod_desc_ofRegion hr hs]
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit A B)
  · rw [← Category.assoc (sumCofan (Φ := Φ) (Γ := []) A B).inl
      (sumIso (Φ := Φ) (Γ := []) A B).hom, sumCofan_inl_sumIso_hom_assoc, coprod.inl_desc]
    rw [← hInl]
    change transportHom J M objIso (J.map (inlMap M A B)) ≫ _ = _
    rw [← transportHom_comp]
    simpa only [packedCopair, ← J.map_comp_assoc, inlMap, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      splitMapCoprod, map_inl_inv_coprodComparison_assoc, coprod.inl_desc] using hf
  · rw [← Category.assoc (sumCofan (Φ := Φ) (Γ := []) A B).inr
      (sumIso (Φ := Φ) (Γ := []) A B).hom, sumCofan_inr_sumIso_hom_assoc, coprod.inr_desc]
    rw [← hInr]
    change transportHom J M objIso (J.map (inrMap M A B)) ≫ _ = _
    rw [← transportHom_comp]
    simpa only [packedCopair, ← J.map_comp_assoc, inrMap, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      splitMapCoprod, map_inr_inv_coprodComparison_assoc, coprod.inr_desc] using hg

set_option backward.isDefEq.respectTransparency false in
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
        (caseValueBranches hr hs)) := by
  rw [case_factor, ← Category.assoc, transportHom_comp, transportHom_comp,
    extend_transport J M objIso f hCopy hWhisker, hDistrib, hf, whiskerLeft_ofRegion,
    packedCopair_transport J M objIso hr hs g h hg hh hInl hInr,
    duplicateArrow, ofRegion_comp, ofRegion_comp, ofRegion_comp]

end Distributive

end Syntactic

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Retained
