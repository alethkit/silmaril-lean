module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Soundness.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Retained.Thms

/-! # Loop-free singleton reification in the Paper quotient -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.PackedBody (applyPacked applyPacked_typed unpack_applyPacked)
open Paper.SingletonReification
open CfgEta.TypeCategory (whiskerLeftRegion_typed)

universe u v w u₁ u₂ u₃ v₁ v₂ v₃

section PurePair

open Silmaril.Isotope.LetIter.Semantics.Categorical (extend_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainedContext)

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] (J : V ⥤ C) [FreydCategory J]

private theorem pure_pair {E F G : V} (f : E ⟶ F) (g : E ⟶ G) :
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair J (J.map f) (J.map g) =
      J.map (CartesianMonoidalCategory.lift f g) := by
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair,
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, retainedContext,
    extend_map, ← J.map_comp]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

end PurePair

section Semantics

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X A D : τ} {p : Region Φ}

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher (denote_weakenCapture)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CartesianMonoidalCategory (fst snd whiskerRight_fst whiskerRight_snd)
open CategoryTheory.MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem lookup0 {Γ : VCtx τ} {D : τ} :
    lookup M 0 (rfl : At (D :: Γ) 0 D) = snd (ctxObj M Γ) (M.obj D) := by
  simp [lookup]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem denote_applyPacked (hp : ValueBranches [Silmaril.product X A] p [D]) :
    denoteRegion J M (applyPacked_typed hp).hasType ≫ J.map (singletonLabelPayload M D) =
      J.map (((λ_ (M.obj X)).hom ▷ M.obj A) ≫ (M.productIso X A).inv) ≫
        denoteSingletonRegion J M hp.hasType := by
  let P := Silmaril.product X A
  let pack := ((λ_ (M.obj X)).hom ▷ M.obj A) ≫ (M.productIso X A).inv
  have hpack := Denotes.pair (Denotes.var (J := J) (M := M) (Φ := Φ) (rfl : At [A, X] 1 X))
    (Denotes.var (J := J) (M := M) (Φ := Φ) (rfl : At [A, X] 0 A))
  have e : CartesianMonoidalCategory.lift (lookup M 1 (rfl : At [A, X] 1 X))
      (lookup M 0 (rfl : At [A, X] 0 A)) = (λ_ (M.obj X)).hom ▷ M.obj A := by
    apply CartesianMonoidalCategory.hom_ext
    · change CartesianMonoidalCategory.lift (fst _ _ ≫ lookup M 0 (rfl : At [X] 0 X))
        (lookup M 0 (rfl : At [A, X] 0 A)) ≫ fst _ _ = _
      simp only [CartesianMonoidalCategory.lift_fst, whiskerRight_fst, lookup0,
        CartesianMonoidalCategory.leftUnitor_hom]
      rfl
    · simp only [CartesianMonoidalCategory.lift_snd, whiskerRight_snd, lookup0]
      rfl
  have d : Denotes J M
      (Tm.HasType.pair (.var (rfl : At [A, X] 1 X)) (.var (rfl : At [A, X] 0 A)) :
        Tm.HasType [A, X] (.pair (.var 1) (.var 0) : Tm Φ) P)
      (J.map pack) := by
    simpa only [pure_pair, e, ← J.map_comp, pack] using hpack
  let t : Tm Φ := .pair (.var 1) (.var 0)
  let hpX := hp.hasType.renameVars ((Ren.wk ([] : VCtx τ) X).lift P)
  let hpXA := hpX.renameVars ((Ren.wk [X] A).lift P)
  obtain ⟨ht, dt⟩ := (denoteRegion_spec J M hpXA).substValue J M d
  have shape : ((p.renameVars (lift Nat.succ)).renameVars (lift Nat.succ)).substVars (Tm.singleSubst t) =
      applyPacked p := by
    simp only [Region.renameVars_comp, Region.substVars_renameVars, applyPacked, t]
    congr 1
    funext i
    cases i <;> rfl
  have deq := (dt.eq_denote J M).symm
  change denoteRegion J M ht = _ at deq
  have congrDenote {r s : Region Φ} (hs : r = s)
      (hr : HasType [A, X] r [D]) (ht : HasType [A, X] s [D]) :
      denoteRegion J M hr = denoteRegion J M ht := by
    subst s
    rfl
  rw [← congrDenote shape ht (applyPacked_typed hp).hasType]
  rw [deq, denote_weakenCapture M J hpX, denote_weakenCapture M J hp.hasType]
  have k : CartesianMonoidalCategory.lift (𝟙 (ctxObj M [A, X])) pack ≫
      (fst (ctxObj M [X]) (M.obj A) ▷ M.obj P) ≫
      (fst (ctxObj M []) (M.obj X) ▷ M.obj P) = pack ≫ (λ_ (M.obj P)).inv := by
    apply CartesianMonoidalCategory.hom_ext
    · change (_ : ctxObj M [A, X] ⟶ 𝟙_ V) = _
      exact Subsingleton.elim _ _
    · simp only [Category.assoc, whiskerRight_snd]
      change CartesianMonoidalCategory.lift (𝟙 (ctxObj M [A, X])) pack ≫
        ((fst (ctxObj M [X]) (M.obj A)) ▷ M.obj P) ≫ snd (ctxObj M [X]) (M.obj P) =
          pack ≫ (λ_ (M.obj P)).inv ≫ snd (𝟙_ V) (M.obj P)
      simp only [whiskerRight_snd,
        ← CartesianMonoidalCategory.leftUnitor_hom, Iso.inv_hom_id, Category.comp_id]
      exact CartesianMonoidalCategory.lift_snd (𝟙 (ctxObj M [A, X])) pack
  simp only [Category.assoc]
  rw [← J.map_comp_assoc, ← J.map_comp_assoc]
  simp only [Category.assoc]
  rw [k]
  simp only [denoteSingletonRegion, pack, J.map_comp, Category.assoc]
  rfl

end Semantics

section Regions

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel bind_pre_map case_pre_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (bind caseWithContext duplicate extend retainLeft splitMapCoprod)
open Paper.TypeCategory
open Paper.RetainedLet (diagonal_typed returnOnce_typed returnOnce_denotation literal_let)
open Paper.RetainedCase (reindexHom returnSum_typed returnSum_denotation packedArms_typed
  literal_case_ofRegion case_ofRegion_inl case_ofRegion_inr distributor_hom_ext
  left_distributor_inl left_distributor_inr)
open CfgEta.TypeCategory.Retained (case_factor packedDistributor packedCopair distributorRegion_typed)
open CfgEta.TypeCategory.ConstructorReification (inlMap inrMap)
open CfgEta.TypeCategory (caseValueBranches seqValueBranches)
open Paper.RetainedLet (unpackBody_typed)
open Region.Paper.SingletonReification.BinaryLet

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

section Model

set_option hygiene false in
local notation "C" => Paper.TypeCategory (τ := τ) Φ
local notation "rBind" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
variable {V : Type u₃} [Category.{v₃} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ ofType (Φ := Φ) T)

variable {X A B D : τ} {a : Tm Φ} {p q : Region Φ}

omit [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M] in
private theorem transport_comp (f : J.obj (M.obj X) ⟶ J.obj (M.obj A))
    (g : J.obj (M.obj A) ⟶ J.obj (M.obj B)) :
    reindexHom J M objIso (f ≫ g) = reindexHom J M objIso f ≫ reindexHom J M objIso g := by
  simp [reindexHom]



set_option backward.isDefEq.respectTransparency false in
omit [FreydCategory.CentralUnit J] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M] in
private theorem extend_compare
    (copy : reindexHom J M objIso (J.map (duplicate (M.obj X) ≫ (M.productIso X X).inv)) =
      ofRegion (τ := τ) (diagonal_typed X))
    (whisker : ∀ {Y A B : τ} (f : J.obj (M.obj A) ⟶ J.obj (M.obj B)),
      reindexHom J M objIso (J.map (M.productIso Y A).hom ≫ retainLeft J (R := M.obj Y) f ≫
        J.map (M.productIso Y B).inv) =
        whiskerLeft (ofType (Φ := Φ) Y) (reindexHom J M objIso f))
    (f : J.obj (M.obj X) ⟶ J.obj (M.obj A)) :
    reindexHom J M objIso (extend J f ≫ J.map (M.productIso X A).inv) =
      ofRegion (τ := τ) (diagonal_typed X) ≫ whiskerLeft (ofType X) (reindexHom J M objIso f) := by
  rw [← copy, ← whisker, ← transport_comp]
  congr 1
  simp [extend, retainLeft, J.map_comp, Category.assoc]

omit [SymmetricCategory V] [HasFiniteCoproducts V] [DistributiveTensor V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M] in
@[reassoc] private theorem whisker_unitor (P Q : V) :
    (λ_ P).inv ▷ Q ≫ (λ_ P).hom ▷ Q = 𝟙 (P ⊗ Q) := by
  rw [← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id, MonoidalCategory.id_whiskerRight]

set_option backward.isDefEq.respectTransparency false in
private theorem denotation_let (ha : Tm.HasType [X] a A)
    (hp : ValueBranches [Silmaril.product X A] p [D]) :
    denoteSingletonRegion J M (.let₁ ha (applyPacked_typed hp).hasType) =
      rBind J (denoteSingletonRegion J M (returnOnce_typed ha).hasType)
        (J.map (M.productIso X A).inv ≫ denoteSingletonRegion J M hp.hasType) := by
  rw [returnOnce_denotation J M ha (denote_spec J M ha)]
  rw [denoteSingletonRegion, ← (RegionDenotes.let₁ (denote_spec J M ha)
    (denoteRegion_spec J M (applyPacked_typed hp).hasType)).eq_denote J M]
  rw [← Category.assoc, ← bind_pre_map J ((λ_ (M.obj X)).inv)]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc, denote_applyPacked J M hp, ← J.map_comp_assoc,
    whisker_unitor_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem denotation_case (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hp : ValueBranches [Silmaril.product X A] p [D])
    (hq : ValueBranches [Silmaril.product X B] q [D]) :
    denoteSingletonRegion J M (.case ha (applyPacked_typed hp).hasType (applyPacked_typed hq).hasType) =
      caseWithContext J
        (denoteSingletonRegion J M (returnSum_typed ha).hasType ≫ J.map (M.coprodIso A B).hom)
        (J.map (M.productIso X A).inv ≫ denoteSingletonRegion J M hp.hasType)
        (J.map (M.productIso X B).inv ≫ denoteSingletonRegion J M hq.hasType) := by
  rw [returnSum_denotation J M ha (denote_spec J M ha)]
  rw [denoteSingletonRegion, ← (RegionDenotes.case (denote_spec J M ha)
    (denoteRegion_spec J M (applyPacked_typed hp).hasType)
    (denoteRegion_spec J M (applyPacked_typed hq).hasType)).eq_denote J M]
  rw [← Category.assoc, ← case_pre_map J ((λ_ (M.obj X)).inv)]
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    Category.assoc, coprod.desc_comp, denote_applyPacked J M hp, denote_applyPacked J M hq,
    ← J.map_comp_assoc, whisker_unitor_assoc]

variable
  (copy : ∀ X : τ, reindexHom J M objIso
    (J.map (duplicate (M.obj X) ≫ (M.productIso X X).inv)) = ofRegion (τ := τ) (diagonal_typed X))
  (whisker : ∀ {Y A B : τ} (f : J.obj (M.obj A) ⟶ J.obj (M.obj B)),
    reindexHom J M objIso (J.map (M.productIso Y A).hom ≫ retainLeft J (R := M.obj Y) f ≫
      J.map (M.productIso Y B).inv) =
      whiskerLeft (ofType (Φ := Φ) Y) (reindexHom J M objIso f))

set_option backward.isDefEq.respectTransparency false in
include copy whisker in
private theorem factor_literal_let₁ (ha : Tm.HasType [X] a A)
    (hp : ValueBranches [Silmaril.product X A] p [D])
    (hf : reindexHom J M objIso (denoteSingletonRegion J M (returnOnce_typed ha).hasType) =
      ofRegion (τ := τ) (returnOnce_typed ha)) :
    reindexHom J M objIso (denoteSingletonRegion J M (.let₁ ha (applyPacked_typed hp).hasType)) =
      (ofRegion (τ := τ) (diagonal_typed X) ≫ whiskerLeft (ofType (Φ := Φ) X)
        (ofRegion (τ := τ) (returnOnce_typed ha))) ≫
        reindexHom J M objIso (denoteSingletonRegion J M hp.hasType) := by
  rw [denotation_let J M ha hp]
  let f := denoteSingletonRegion J M (returnOnce_typed ha).hasType
  let g := denoteSingletonRegion J M hp.hasType
  change reindexHom J M objIso (extend J f ≫ J.map (M.productIso X A).inv ≫ g) = _
  rw [← Category.assoc, transport_comp, extend_compare J M objIso (copy X) whisker, hf]

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M] in
theorem assemble_let₁ (ha : Tm.HasType [X] a A)
    (hp : ValueBranches [Silmaril.product X A] p [D]) :
    (ofRegion (τ := τ) (diagonal_typed X) ≫ whiskerLeft (ofType (Φ := Φ) X)
      (ofRegion (τ := τ) (returnOnce_typed ha))) ≫ ofRegion (τ := τ) hp =
        ofRegion (τ := τ) (.let₁ ha (applyPacked_typed hp)) := by
  have e : ofRegion (τ := τ) (unpackBody_typed (applyPacked_typed hp)) = ofRegion (τ := τ) hp :=
    (ofRegion_eq_iff _ _).2 (unpack_applyPacked hp)
  let hx := seqValueBranches (diagonal_typed (Φ := Φ) X)
    (whiskerLeftRegion_typed X (returnOnce_typed ha))
  let hy := unpackBody_typed (applyPacked_typed hp)
  rw [← e, whiskerLeft_ofRegion, ofRegion_comp _ _ hx, ofRegion_comp hx hy (seqValueBranches hx hy)]
  exact (ofRegion_eq_iff _ _).2 (literal_let ha (applyPacked_typed hp).hasType)

set_option backward.isDefEq.respectTransparency false in
include copy whisker in
private theorem compare_let (ha : Tm.HasType [X] a A)
    (hp : ValueBranches [Silmaril.product X A] p [D])
    (hf : reindexHom J M objIso (denoteSingletonRegion J M (returnOnce_typed ha).hasType) =
      ofRegion (τ := τ) (returnOnce_typed ha))
    (hg : reindexHom J M objIso (denoteSingletonRegion J M hp.hasType) = ofRegion (τ := τ) hp) :
    reindexHom J M objIso (denoteSingletonRegion J M (.let₁ ha (applyPacked_typed hp).hasType)) =
      ofRegion (τ := τ) (.let₁ ha (applyPacked_typed hp)) := by
  rw [factor_literal_let₁ J M objIso copy whisker ha hp hf, hg, assemble_let₁ ha hp]

set_option backward.isDefEq.respectTransparency false in
include copy whisker in
private theorem factor_literal_let₂ (ha : Tm.HasType [X] a (Silmaril.product A B))
    (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]) :
    reindexHom J M objIso (denoteSingletonRegion J M (.let₂ ha (applyPackedPair_typed hp).hasType)) =
      (ofRegion (τ := τ) (diagonal_typed X) ≫ whiskerLeft (ofType (Φ := Φ) X)
        (reindexHom J M objIso (denoteSingletonRegion J M (returnPair_typed ha).hasType))) ≫
        reindexHom J M objIso (denoteSingletonRegion J M hp.hasType) := by
  rw [denote_literal_let₂ J M ha hp, ← Category.assoc, transport_comp,
    extend_compare J M objIso (copy X) whisker]

set_option backward.isDefEq.respectTransparency false in
include copy whisker in
private theorem compare_literal_let₂ (ha : Tm.HasType [X] a (Silmaril.product A B))
    (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D])
    (hf : reindexHom J M objIso (denoteSingletonRegion J M (returnPair_typed ha).hasType) =
      ofRegion (τ := τ) (returnPair_typed ha))
    (hg : reindexHom J M objIso (denoteSingletonRegion J M hp.hasType) = ofRegion (τ := τ) hp) :
    reindexHom J M objIso (denoteSingletonRegion J M (.let₂ ha (applyPackedPair_typed hp).hasType)) =
      ofRegion (τ := τ) (.let₂ ha (applyPackedPair_typed hp)) := by
  rw [factor_literal_let₂ J M objIso copy whisker ha hp, hf, hg, whiskerLeft_ofRegion]
  let h := seqValueBranches (diagonal_typed (Φ := Φ) X) (whiskerLeftRegion_typed X (returnPair_typed ha))
  rw [ofRegion_comp _ _ h, ofRegion_comp h hp (seqValueBranches h hp)]
  exact (ofRegion_eq_iff _ _).2 (literal_let₂ ha hp)

variable
  (inl : ∀ A B : τ, reindexHom J M objIso (J.map (inlMap M A B)) = (sumCofan (Φ := Φ) A B).inl)
  (inr : ∀ A B : τ, reindexHom J M objIso (J.map (inrMap M A B)) = (sumCofan (Φ := Φ) A B).inr)
  (distributor : ∀ X A B : τ, reindexHom J M objIso (J.map (packedDistributor M X A B)) =
    ofRegion (τ := τ) (distributorRegion_typed X A B))

set_option backward.isDefEq.respectTransparency false in
include inl inr in
omit [FreydCategory.CentralUnit J] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M] in
theorem compare_copair {l r : Region Φ} (hl : ValueBranches [A] l [D])
    (hr : ValueBranches [B] r [D])
    {f : J.obj (M.obj A) ⟶ J.obj (M.obj D)} {g : J.obj (M.obj B) ⟶ J.obj (M.obj D)}
    (hf : reindexHom J M objIso f = ofRegion (τ := τ) hl)
    (hg : reindexHom J M objIso g = ofRegion (τ := τ) hr) :
    reindexHom J M objIso (packedCopair J M f g) = ofRegion (τ := τ) (caseValueBranches hl hr) := by
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit A B)
  · rw [case_ofRegion_inl hl hr, ← inl, ← transport_comp, ← hf]
    congr 1
    simp only [packedCopair, ← J.map_comp_assoc, inlMap, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, splitMapCoprod, map_inl_inv_coprodComparison_assoc, coprod.inl_desc]
  · rw [case_ofRegion_inr hl hr, ← inr, ← transport_comp, ← hg]
    congr 1
    simp only [packedCopair, ← J.map_comp_assoc, inrMap, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, splitMapCoprod, map_inr_inv_coprodComparison_assoc, coprod.inr_desc]

set_option backward.isDefEq.respectTransparency false in
include copy whisker distributor in
private theorem factor_literal_case (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hp : ValueBranches [Silmaril.product X A] p [D])
    (hq : ValueBranches [Silmaril.product X B] q [D])
    (hf : reindexHom J M objIso (denoteSingletonRegion J M (returnSum_typed ha).hasType) =
      ofRegion (τ := τ) (returnSum_typed ha)) :
    reindexHom J M objIso (denoteSingletonRegion J M
      (.case ha (applyPacked_typed hp).hasType (applyPacked_typed hq).hasType)) =
      ((ofRegion (τ := τ) (diagonal_typed X) ≫ whiskerLeft (ofType (Φ := Φ) X)
          (ofRegion (τ := τ) (returnSum_typed ha))) ≫
        ofRegion (τ := τ) (distributorRegion_typed X A B)) ≫
      reindexHom J M objIso (packedCopair J M
        (denoteSingletonRegion J M hp.hasType) (denoteSingletonRegion J M hq.hasType)) := by
  rw [denotation_case J M ha hp hq, case_factor, ← Category.assoc, transport_comp, transport_comp,
    extend_compare J M objIso (copy X) whisker, hf, distributor]

set_option backward.isDefEq.respectTransparency false in
include copy whisker inl inr distributor in
private theorem compare_case (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hp : ValueBranches [Silmaril.product X A] p [D])
    (hq : ValueBranches [Silmaril.product X B] q [D])
    (hf : reindexHom J M objIso (denoteSingletonRegion J M (returnSum_typed ha).hasType) =
      ofRegion (τ := τ) (returnSum_typed ha))
    (hg : reindexHom J M objIso (denoteSingletonRegion J M hp.hasType) = ofRegion (τ := τ) hp)
    (hh : reindexHom J M objIso (denoteSingletonRegion J M hq.hasType) = ofRegion (τ := τ) hq) :
    reindexHom J M objIso (denoteSingletonRegion J M
      (.case ha (applyPacked_typed hp).hasType (applyPacked_typed hq).hasType)) =
      ofRegion (τ := τ) (.case ha (applyPacked_typed hp) (applyPacked_typed hq)) := by
  rw [factor_literal_case J M objIso copy whisker distributor ha hp hq hf]
  rw [compare_copair J M objIso inl inr (unpackBody_typed (applyPacked_typed hp))
    (unpackBody_typed (applyPacked_typed hq))
    (hg.trans ((ofRegion_eq_iff _ hp).2 (unpack_applyPacked hp)).symm)
    (hh.trans ((ofRegion_eq_iff _ hq).2 (unpack_applyPacked hq)).symm)]
  exact literal_case_ofRegion ha (applyPacked_typed hp) (applyPacked_typed hq)

variable
  (constructorReturn : ∀ {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A),
    reindexHom J M objIso (denoteSingletonRegion J M (HasType.br (ℓ := 0) rfl ha.hasType)) =
      ofRegion (τ := τ) (.br (ℓ := 0) rfl ha))
  (producerReturn : ∀ {X A : τ} {a : Tm Φ} (ha : Tm.HasType [X] a A),
    reindexHom J M objIso (denoteSingletonRegion J M (returnOnce_typed ha).hasType) =
      ofRegion (τ := τ) (returnOnce_typed ha))
  (sumReturn : ∀ {X A B : τ} {a : Tm Φ} (ha : Tm.HasType [X] a (Silmaril.coprod A B)),
    reindexHom J M objIso (denoteSingletonRegion J M (returnSum_typed ha).hasType) =
      ofRegion (τ := τ) (returnSum_typed ha))

set_option backward.isDefEq.respectTransparency false in
include copy whisker inl inr distributor constructorReturn producerReturn sumReturn in
private theorem compare_loopFree {r : Region Φ} {hr : ValueBranches [X] r [D]} (h : LoopFree hr) :
    reindexHom J M objIso (denoteSingletonRegion J M hr.hasType) = ofRegion (τ := τ) hr := by
  induction h with
  | branch ha => exact constructorReturn ha
  | let₁ ha _ ih => exact compare_let J M objIso copy whisker ha _ (producerReturn ha) ih
  | let₂ ha producer _ ih =>
    apply compare_literal_let₂ J M objIso copy whisker ha _ ?_ ih
    rw [returnPair_denotation J M ha, producerReturn ha]
    exact ((ofRegion_eq_iff (returnPair_typed ha) (returnOnce_typed ha)).2 producer).symm
  | case ha _ _ ihl ihr =>
    exact compare_case J M objIso copy whisker inl inr distributor ha _ _ (sumReturn ha) ihl ihr
  | @cfgZero X D p hp _ blocks ih =>
    rw [denoteSingletonRegion_cfgZero J M hp.hasType blocks, ih]
    apply (ofRegion_eq_iff _ _).2
    exact .symm (.cfgEta (.native (.base (.entry (.cfgZero hp.hasType blocks)))))

omit [SymmetricCategory V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M] in
private theorem source_distributor_inl :
    (M.productIso X A).hom ≫ (M.obj X ◁ inlMap M A B) ≫
      (M.productIso X (Silmaril.coprod A B)).inv ≫ packedDistributor M X A B =
    inlMap M (Silmaril.product X A) (Silmaril.product X B) := by
  unfold packedDistributor inlMap
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.inv_hom_id, Category.comp_id]
  have h : (M.obj X ◁ (coprod.inl : M.obj A ⟶ M.obj A ⨿ M.obj B)) ≫
      (DistributiveTensor.leftIso (M.obj X) (M.obj A) (M.obj B)).inv = coprod.inl := by
    rw [← DistributiveTensor.inl_leftHom]
    let e := DistributiveTensor.leftIso (M.obj X) (M.obj A) (M.obj B)
    change (coprod.inl ≫ e.hom) ≫ e.inv = _
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [← Category.assoc _ (DistributiveTensor.leftIso _ _ _).inv, h, coprod.inl_map_assoc,
    Iso.hom_inv_id_assoc]

omit [SymmetricCategory V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M] in
private theorem source_distributor_inr :
    (M.productIso X B).hom ≫ (M.obj X ◁ inrMap M A B) ≫
      (M.productIso X (Silmaril.coprod A B)).inv ≫ packedDistributor M X A B =
    inrMap M (Silmaril.product X A) (Silmaril.product X B) := by
  unfold packedDistributor inrMap
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.inv_hom_id, Category.comp_id]
  have h : (M.obj X ◁ (coprod.inr : M.obj B ⟶ M.obj A ⨿ M.obj B)) ≫
      (DistributiveTensor.leftIso (M.obj X) (M.obj A) (M.obj B)).inv = coprod.inr := by
    rw [← DistributiveTensor.inr_leftHom]
    let e := DistributiveTensor.leftIso (M.obj X) (M.obj A) (M.obj B)
    change (coprod.inr ≫ e.hom) ≫ e.inv = _
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [← Category.assoc _ (DistributiveTensor.leftIso _ _ _).inv, h, coprod.inr_map_assoc,
    Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
omit [FreydCategory.CentralUnit J] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M] in
private theorem retain_pure {R S T : V} (f : S ⟶ T) :
    retainLeft J (R := R) (J.map f) = J.map (R ◁ f) := by
  simp [retainLeft, PremonoidalCategory.leftTensor, Functor.StrongPremonoidal.tensor_naturality_right]

set_option backward.isDefEq.respectTransparency false in
include whisker inl inr in
omit [FreydCategory.CentralUnit J] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M] in
private theorem compare_distributor :
    reindexHom J M objIso (J.map (packedDistributor M X A B)) =
      ofRegion (τ := τ) (distributorRegion_typed X A B) := by
  apply distributor_hom_ext
  · rw [left_distributor_inl, ← inl A B, ← whisker, retain_pure, ← J.map_comp_assoc,
      ← J.map_comp, ← transport_comp, ← J.map_comp]
    simp only [Category.assoc]
    exact congrArg (fun f => reindexHom J M objIso (J.map f)) (source_distributor_inl (B := B) M) |>.trans
      (inl (Silmaril.product X A) (Silmaril.product X B))
  · rw [left_distributor_inr, ← inr A B, ← whisker, retain_pure, ← J.map_comp_assoc,
      ← J.map_comp, ← transport_comp, ← J.map_comp]
    simp only [Category.assoc]
    exact congrArg (fun f => reindexHom J M objIso (J.map f)) (source_distributor_inr (A := A) M) |>.trans
      (inr (Silmaril.product X A) (Silmaril.product X B))

end Model

end Regions

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)
open Paper.TypeCategory
open Paper.RetainedCase (reindexHom)
open Paper.RetainedLet (diagonal_typed)
open CfgEta.TypeCategory (productFstBranches productSndBranches returnRegion_branchValue seqValueBranches)
open CfgEta.TypeCategory.ConstructorReification (unitMap fstMap sndMap inlMap inrMap)

section Constructors

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₃} [Category.{v₃} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (J : V ⥤ Paper.TypeCategory (τ := τ) Φ) (M : TypeModel τ V)
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ ofType (Φ := Φ) T)
  {X A B : τ}
  {ε : Type w} [HasEff Φ ε] (pe : ε)

private abbrev branch {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    ofType (Φ := Φ) X ⟶ ofType A :=
  ofRegion (τ := τ) (.br (ℓ := 0) rfl ha)

private theorem branch_pure {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    PureReturn pe (branch ha) := by
  have h : returnTerm ha.hasType = branch ha :=
    (ofRegion_eq_iff _ _).2 (.cfgEta (.native (.base (returnRegion_branchValue ha))))
  rw [← h]
  apply pureReturn_returnTerm
  clear h
  induction ha <;> constructor <;> assumption

variable
  (fstAgrees : ∀ A B : τ, reindexHom J M objIso (J.map (fstMap M A B)) =
    ofRegion (τ := τ) (productFstBranches A B))
  (sndAgrees : ∀ A B : τ, reindexHom J M objIso (J.map (sndMap M A B)) =
    ofRegion (τ := τ) (productSndBranches A B))
  (imagePure : ∀ {X A : τ} (f : M.obj X ⟶ M.obj A),
    PureReturn pe (reindexHom J M objIso (J.map f)))
  (projectionExtensionality : ∀ {X A B : τ}
    {f g : ofType (Φ := Φ) X ⟶ ofType (Silmaril.product A B)},
    PureReturn pe f → PureReturn pe g →
    f ≫ ofRegion (τ := τ) (productFstBranches A B) = g ≫ ofRegion (τ := τ) (productFstBranches A B) →
    f ≫ ofRegion (τ := τ) (productSndBranches A B) = g ≫ ofRegion (τ := τ) (productSndBranches A B) → f = g)

set_option backward.isDefEq.respectTransparency false in
include fstAgrees sndAgrees imagePure projectionExtensionality in
private theorem compare_pair {a b : Tm Φ} (ha : Tm.BranchValue [X] a A)
    (hb : Tm.BranchValue [X] b B) (f : M.obj X ⟶ M.obj A) (g : M.obj X ⟶ M.obj B)
    (hf : reindexHom J M objIso (J.map f) = branch ha)
    (hg : reindexHom J M objIso (J.map g) = branch hb) :
    reindexHom J M objIso (J.map (CartesianMonoidalCategory.lift f g ≫ (M.productIso A B).inv)) =
      branch (.pair ha hb) := by
  apply projectionExtensionality (imagePure _) (branch_pure pe (.pair ha hb))
  · rw [← fstAgrees, ← transport_comp, ← J.map_comp]
    simp only [fstMap, Category.assoc, Iso.inv_hom_id_assoc, CartesianMonoidalCategory.lift_fst, hf]
    have e : Paper.Eqv [X] (.let₂ (.pair a b) (.br 0 (.var 1))) (.br 0 a) [A] :=
      .productBeta (.let₂Beta ha hb (.br (rfl : At [A] 0 A) (.var (i := 1) rfl)))
    rw [← fstMap, fstAgrees A B]
    let hp := productFstBranches (Φ := Φ) A B
    let hb' : ValueBranches [X] (.br 0 (.pair a b)) [Silmaril.product A B] := .br rfl (.pair ha hb)
    rw [ofRegion_comp hb' hp (seqValueBranches hb' hp)]
    exact (ofRegion_eq_iff _ _).2 (Paper.Eqv.symm e)
  · rw [← sndAgrees, ← transport_comp, ← J.map_comp]
    simp only [sndMap, Category.assoc, Iso.inv_hom_id_assoc, CartesianMonoidalCategory.lift_snd, hg]
    have e : Paper.Eqv [X] (.let₂ (.pair a b) (.br 0 (.var 0))) (.br 0 b) [B] :=
      .productBeta (.let₂Beta ha hb (.br (rfl : At [B] 0 B) (.var (i := 0) rfl)))
    rw [← sndMap, sndAgrees A B]
    let hp := productSndBranches (Φ := Φ) A B
    let hb' : ValueBranches [X] (.br 0 (.pair a b)) [Silmaril.product A B] := .br rfl (.pair ha hb)
    rw [ofRegion_comp hb' hp (seqValueBranches hb' hp)]
    exact (ofRegion_eq_iff _ _).2 (Paper.Eqv.symm e)

set_option backward.isDefEq.respectTransparency false in
include fstAgrees sndAgrees imagePure projectionExtensionality in
private theorem compare_diagonal :
    reindexHom J M objIso (J.map (duplicate (M.obj X) ≫ (M.productIso X X).inv)) =
      ofRegion (τ := τ) (diagonal_typed X) := by
  have h : reindexHom J M objIso (J.map (𝟙 (M.obj X))) =
      branch (.var rfl : Tm.BranchValue [X] (.var 0 : Tm Φ) X) := by
    change _ = ofRegion (r := .br 0 (.var 0)) _
    rw [ofRegion_id]
    simp [reindexHom]
  exact compare_pair J M objIso pe fstAgrees sndAgrees imagePure projectionExtensionality
    (.var rfl) (.var rfl) _ _ h h

variable
  (unitAgrees : ∀ X : τ, reindexHom J M objIso (J.map (unitMap M X)) =
    ofRegion (τ := τ) (.br (ℓ := 0) (A := Silmaril.unit) rfl (.unit (Γ := [X]))))
  (inlAgrees : ∀ A B : τ, reindexHom J M objIso (J.map (inlMap M A B)) =
    (sumCofan (Φ := Φ) A B).inl)
  (inrAgrees : ∀ A B : τ, reindexHom J M objIso (J.map (inrMap M A B)) =
    (sumCofan (Φ := Φ) A B).inr)
variable [SymmetricCategory V]
  [PremonoidalCategory (Paper.TypeCategory (τ := τ) Φ)]
  [SymmetricPremonoidalCategory (Paper.TypeCategory (τ := τ) Φ)]
  [HasFiniteCoproducts (Paper.TypeCategory (τ := τ) Φ)]
  [DistributiveTensor V] [DistributivePremonoidalCategory (Paper.TypeCategory (τ := τ) Φ)]
  [DistributiveFreydCategory J] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
include unitAgrees fstAgrees sndAgrees inlAgrees inrAgrees imagePure projectionExtensionality in
private theorem compare_constructor_graph {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    ∃ f : ctxObj M [X] ⟶ M.obj A, Denotes J M ha.hasType (J.map f) ∧
      reindexHom J M objIso (J.map (((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫ f)) =
        branch ha := by
  induction ha with
  | @var i A hi =>
    cases i with
    | zero =>
      have e : X = A := Option.some.inj hi
      subst A
      refine ⟨_, Denotes.var hi, ?_⟩
      have e : lookup M 0 hi = (λ_ (M.obj X)).hom := by
        change snd (𝟙_ V) (M.obj X) = _
        rw [CartesianMonoidalCategory.leftUnitor_hom]
      change _ = ofRegion (r := .br 0 (.var 0)) _
      rw [e, Iso.inv_hom_id, ofRegion_id]
      simp [reindexHom]
    | succ i => simp [At] at hi
  | unit =>
    refine ⟨CartesianMonoidalCategory.toUnit (ctxObj M [X]) ≫ M.unitIso.inv, Denotes.unit, ?_⟩
    have e : ((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫
        CartesianMonoidalCategory.toUnit (ctxObj M [X]) = CartesianMonoidalCategory.toUnit (M.obj X) :=
      Subsingleton.elim _ _
    calc
      _ = reindexHom J M objIso (J.map (unitMap M X)) := by
        unfold unitMap
        rw [← Category.assoc, e]
      _ = _ := unitAgrees X
  | @pair a A b B ha hb iha ihb =>
    obtain ⟨f, df, hf⟩ := iha
    obtain ⟨g, dg, hg⟩ := ihb
    refine ⟨CartesianMonoidalCategory.lift f g ≫ (M.productIso A B).inv, ?_, ?_⟩
    · simpa only [pure_pair, ← J.map_comp] using Denotes.pair df dg
    · rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
      exact compare_pair J M objIso pe fstAgrees sndAgrees imagePure projectionExtensionality ha hb _ _ hf hg
  | @inl a A B ha iha =>
    obtain ⟨f, df, hf⟩ := iha
    refine ⟨f ≫ inlMap M A B, ?_, ?_⟩
    · simpa only [inlMap, J.map_comp] using Denotes.inl (B := B) df
    · rw [← Category.assoc, J.map_comp, transport_comp, hf, inlAgrees, sumCofan_inl]
      rfl
  | @inr b B A hb ihb =>
    obtain ⟨g, dg, hg⟩ := ihb
    refine ⟨g ≫ inrMap M A B, ?_, ?_⟩
    · simpa only [inrMap, J.map_comp] using Denotes.inr (A := A) dg
    · rw [← Category.assoc, J.map_comp, transport_comp, hg, inrAgrees, sumCofan_inr]
      rfl

end Constructors

section Assembly

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)
open Paper.TypeCategory
open Paper.RetainedLet (returnOnce_typed)
open Paper.RetainedCase (reindexHom returnSum_typed)
open CfgEta.TypeCategory (productFstBranches productSndBranches)
open CfgEta.TypeCategory.ConstructorReification (unitMap fstMap sndMap inlMap inrMap)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₃} [Category.{v₃} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

variable
  [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp]
  [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ ofType (Φ := Φ) T)
  {ε : Type w} [HasEff Φ ε] (pe : ε)

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]
  {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [D]}

set_option backward.isDefEq.respectTransparency false in
theorem compare (cmp : ModelComparisons J M objIso pe) (h : LoopFree hr) :
    reindexHom J M objIso (denoteSingletonRegion J M hr.hasType) = ofRegion (τ := τ) hr := by
  apply compare_loopFree J M objIso
    (fun X => compare_diagonal (X := X) J M objIso pe cmp.fst cmp.snd cmp.imagePure cmp.projectionExtensionality)
    (fun {Y A B} f => cmp.whisker (Y := Y) (A := A) (B := B) f) cmp.inl cmp.inr
    (fun _ _ _ => compare_distributor J M objIso (fun {Y A B} f => cmp.whisker (Y := Y) (A := A) (B := B) f) cmp.inl cmp.inr)
    ?_ (fun {_ _ _} ha => cmp.producer ha) (fun {_ _ _ _} ha => cmp.sumProducer ha) h
  intro X A a ha
  obtain ⟨f, df, hf⟩ := compare_constructor_graph J M objIso pe cmp.fst cmp.snd
    cmp.imagePure cmp.projectionExtensionality cmp.unit cmp.inl cmp.inr ha
  simpa only [denoteSingletonRegion_br J M df, J.map_comp] using hf

theorem compare_of_eqv (cmp : ModelComparisons J M objIso pe)
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {s : Region Φ} (hs : ValueBranches [X] s [D]) (h : LoopFree hr) (e : Paper.Eqv [X] s r [D]) :
    reindexHom J M objIso (denoteSingletonRegion J M hs.hasType) = ofRegion (τ := τ) hs := by
  have hd : denoteSingletonRegion J M hs.hasType = denoteSingletonRegion J M hr.hasType := by
    unfold denoteSingletonRegion
    rw [e.sound J M shared hs.hasType hr.hasType]
  rw [hd, compare J M objIso pe cmp h, (ofRegion_eq_iff hs hr).2 e]

open CfgEta.TypeCategory.Retained (packedCopair distributorRegion_typed)
open Paper.RetainedLet (diagonal_typed)

set_option backward.isDefEq.respectTransparency false in
theorem factor_let₁ (cmp : ModelComparisons J M objIso pe)
    {A : τ} {a : Tm Φ} {p : Region Φ} (ha : Tm.HasType [X] a A)
    (hp : ValueBranches [Silmaril.product X A] p [D]) :
    reindexHom J M objIso (denoteSingletonRegion J M (.let₁ ha (applyPacked_typed hp).hasType)) =
      (ofRegion (τ := τ) (diagonal_typed X) ≫ whiskerLeft (ofType (Φ := Φ) X)
        (ofRegion (τ := τ) (returnOnce_typed ha))) ≫
        reindexHom J M objIso (denoteSingletonRegion J M hp.hasType) :=
  factor_literal_let₁ J M objIso
    (fun X => compare_diagonal (X := X) J M objIso pe cmp.fst cmp.snd cmp.imagePure cmp.projectionExtensionality)
    (fun {Y A B} f => cmp.whisker (Y := Y) (A := A) (B := B) f) ha hp (cmp.producer ha)

set_option backward.isDefEq.respectTransparency false in
theorem factor_case (cmp : ModelComparisons J M objIso pe)
    {A B : τ} {a : Tm Φ} {p q : Region Φ} (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hp : ValueBranches [Silmaril.product X A] p [D])
    (hq : ValueBranches [Silmaril.product X B] q [D]) :
    reindexHom J M objIso (denoteSingletonRegion J M
      (.case ha (applyPacked_typed hp).hasType (applyPacked_typed hq).hasType)) =
      ((ofRegion (τ := τ) (diagonal_typed X) ≫ whiskerLeft (ofType (Φ := Φ) X)
          (ofRegion (τ := τ) (returnSum_typed ha))) ≫
        ofRegion (τ := τ) (distributorRegion_typed X A B)) ≫
      reindexHom J M objIso (packedCopair J M
        (denoteSingletonRegion J M hp.hasType) (denoteSingletonRegion J M hq.hasType)) :=
  factor_literal_case J M objIso
    (fun X => compare_diagonal (X := X) J M objIso pe cmp.fst cmp.snd cmp.imagePure cmp.projectionExtensionality)
    (fun {Y A B} f => cmp.whisker (Y := Y) (A := A) (B := B) f)
    (fun _ _ _ => compare_distributor J M objIso
      (fun {Y A B} f => cmp.whisker (Y := Y) (A := A) (B := B) f) cmp.inl cmp.inr)
    ha hp hq (cmp.sumProducer ha)

section BinaryLet

open Region.Paper.SingletonReification.BinaryLet

variable {A B : τ} {a : Tm Φ} {p : Region Φ}

set_option backward.isDefEq.respectTransparency false in
/-- Factor the interpreted binary let through the single-bind producer and the interpreted packed body. -/
theorem factor_let₂ (cmp : ModelComparisons J M objIso pe)
    (ha : Tm.HasType [X] a (Silmaril.product A B))
    (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]) :
    reindexHom J M objIso (denoteSingletonRegion J M (.let₂ ha (applyPackedPair_typed hp).hasType)) =
      (ofRegion (τ := τ) (Paper.RetainedLet.diagonal_typed X) ≫ whiskerLeft (ofType (Φ := Φ) X)
        (ofRegion (τ := τ) (returnOnce_typed ha))) ≫
        reindexHom J M objIso (denoteSingletonRegion J M hp.hasType) := by
  have hCopy := fun X => compare_diagonal (X := X) J M objIso pe cmp.fst cmp.snd
    cmp.imagePure cmp.projectionExtensionality
  rw [factor_literal_let₂ J M objIso hCopy (fun {Y A B} f => cmp.whisker (Y := Y) (A := A) (B := B) f)
    ha hp, returnPair_denotation J M ha, cmp.producer ha]

set_option backward.isDefEq.respectTransparency false in
theorem returnPair_comparison_iff (cmp : ModelComparisons J M objIso pe)
    (ha : Tm.HasType [X] a (Silmaril.product A B)) :
    (reindexHom J M objIso (denoteSingletonRegion J M (returnPair_typed ha).hasType) =
      ofRegion (τ := τ) (returnPair_typed ha)) ↔
      Paper.Eqv [X] (returnPair a) (Paper.RetainedLet.returnOnce a) [Silmaril.product A B] := by
  rw [returnPair_denotation J M ha, cmp.producer ha]
  exact eq_comm.trans (ofRegion_eq_iff (returnPair_typed ha) (returnOnce_typed ha))

set_option backward.isDefEq.respectTransparency false in
theorem compare_let₂ (cmp : ModelComparisons J M objIso pe)
    (ha : Tm.HasType [X] a (Silmaril.product A B))
    (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D])
    (hProducer : Paper.Eqv [X] (returnPair a) (Paper.RetainedLet.returnOnce a) [Silmaril.product A B])
    (hBody : reindexHom J M objIso (denoteSingletonRegion J M hp.hasType) = ofRegion (τ := τ) hp) :
    reindexHom J M objIso (denoteSingletonRegion J M (.let₂ ha (applyPackedPair_typed hp).hasType)) =
      ofRegion (τ := τ) (.let₂ ha (applyPackedPair_typed hp)) := by
  have hPair := (returnPair_comparison_iff J M objIso pe cmp ha).2 hProducer
  exact compare_literal_let₂ J M objIso
    (fun X => compare_diagonal (X := X) J M objIso pe cmp.fst cmp.snd cmp.imagePure cmp.projectionExtensionality)
    (fun {Y A B} f => cmp.whisker (Y := Y) (A := A) (B := B) f) ha hp hPair hBody

end BinaryLet

end Assembly

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification
