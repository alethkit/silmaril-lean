module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators

/-! # Proofs of constructor-value reification -/

public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open Silmaril
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w u₁ v₁

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues

open CfgEta CfgEta.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

variable {X A B D : τ} {a b : Tm Φ} {r s : Region Φ}

theorem branchArrow_eq_return (ha : Tm.BranchValue [X] a A) :
    branchArrow ha = ofRegion (returnRegion_typed ha.hasType) :=
  (ofRegion_eq_iff _ _).2 (.symm (.native (.base (returnRegion_branchValue ha))))

theorem branchArrow_var : branchArrow (.var (i := 0) (rfl : At [X] 0 X) :
    Tm.BranchValue [X] (.var 0 : Tm Φ) X) = 𝟙 (ofType X) :=
  ofRegion_identity X

theorem ofRegion_comp (hr : ValueBranches [X] r [A]) (hs : ValueBranches [A] s [B]) :
    ofRegion hr ≫ ofRegion hs = ofRegion (seqValueBranches hr hs) := by
  apply (ofRegion_eq_iff (seqValueBranches hr hs) (seqValueBranches hr hs)).2
  exact .native (.base (.refl (seqValueBranches hr hs).hasType))

theorem branchArrow_inl (ha : Tm.BranchValue [X] a A) (B : τ) :
    branchArrow ha ≫ (sumCofan (Φ := Φ) (Γ := []) A B).inl =
      branchArrow (.inl (B := B) ha) := by
  rw [sumCofan_inl]
  change ofRegion _ ≫ ofRegion _ = _
  exact ofRegion_comp _ _

theorem branchArrow_inr (B : τ) (ha : Tm.BranchValue [X] a A) :
    branchArrow ha ≫ (sumCofan (Φ := Φ) (Γ := []) B A).inr =
      branchArrow (.inr (A := B) ha) := by
  rw [sumCofan_inr]
  change ofRegion _ ≫ ofRegion _ = _
  exact ofRegion_comp _ _

theorem branchPair_fst_beta (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    ProductBeta.Eqv [X] (.let₂ (.pair a b) (.br 0 (.var 1))) (.br 0 a) [A] :=
  .ofStep (.let₂Beta ha hb (.br (rfl : At [A] 0 A) (.var (i := 1) rfl)))

theorem branchPair_snd_beta (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    ProductBeta.Eqv [X] (.let₂ (.pair a b) (.br 0 (.var 0))) (.br 0 b) [B] :=
  .ofStep (.let₂Beta ha hb (.br (rfl : At [B] 0 B) (.var (i := 0) rfl)))

theorem branchArrow_pair_fst
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B)
    (h : Eqv [X] (.let₂ (.pair a b) (.br 0 (.var 1))) (.br 0 a) [A]) :
    branchArrow (.pair ha hb) ≫ productFst A B = branchArrow ha := by
  rw [branchArrow, productFst, ofRegion_comp]
  exact (ofRegion_eq_iff _ _).2 h

theorem branchArrow_pair_snd
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B)
    (h : Eqv [X] (.let₂ (.pair a b) (.br 0 (.var 0))) (.br 0 b) [B]) :
    branchArrow (.pair ha hb) ≫ productSnd A B = branchArrow hb := by
  rw [branchArrow, productSnd, ofRegion_comp]
  exact (ofRegion_eq_iff _ _).2 h

theorem packedLookupRegion_typed {Γ Δ : VCtx τ} {i j : Nat} (hi : At Γ i A)
    (hj : At Δ j (packedInputType Γ)) :
    ValueBranches Δ (packedLookupRegion j i : Region Φ) [A] := by
  induction Γ generalizing Δ i j with
  | nil => simp [At] at hi
  | cons B Γ ih =>
    cases i with
    | zero =>
      have h : B = A := Option.some.inj hi
      subst A
      exact .let₂ (.var hj) (.br rfl (.var (i := 0) rfl))
    | succ i =>
      exact .let₂ (.var hj) (ih (Δ := B :: packedInputType Γ :: Δ) (j := 1) hi rfl)

private theorem packedLookupRegion_rename (j i : Nat) (ρ : Nat → Nat) :
    (packedLookupRegion j i : Region Φ).renameVars ρ = packedLookupRegion (ρ j) i := by
  induction i generalizing j ρ with
  | zero => rfl
  | succ i ih =>
    simp only [packedLookupRegion, renameVars, Tm.rename, ih]
    rfl

private theorem packedLookupRegion_subst (j i k : Nat) (σ : Nat → Tm Φ)
    (h : σ j = .var k) :
    (packedLookupRegion j i : Region Φ).substVars σ = packedLookupRegion k i := by
  induction i generalizing j k σ with
  | zero => simp only [packedLookupRegion, substVars, Tm.subst, h]; rfl
  | succ i ih =>
    simp only [packedLookupRegion, substVars, Tm.subst, h]
    rw [ih 1 1 (Tm.liftSubstN 2 σ) rfl]

set_option backward.isDefEq.respectTransparency false in
theorem packedLookup_eq_ofRegion (Γ : VCtx τ) (i : Nat) (hi : At Γ i A) :
    packedLookup (Φ := Φ) Γ i hi =
      ofRegion (packedLookupRegion_typed (Φ := Φ) hi (show At [packedInputType Γ] 0 _ from rfl)) := by
  induction Γ generalizing i with
  | nil => simp [At] at hi
  | cons B Γ ih =>
    cases i with
    | zero =>
      have h : B = A := Option.some.inj hi
      subst A
      rfl
    | succ i =>
      rw [packedLookup, ih i hi, productFst, ofRegion_comp]
      apply (ofRegion_eq_iff _ _).2
      have eq :
          (Region.let₂ (.var 0) (.br 0 (.var 1)) : Region Φ).lsubst
            (fun _ => (packedLookupRegion 0 i : Region Φ).renameVars (Silmaril.DeBruijn.lift Nat.succ)) =
          packedLookupRegion 0 (i + 1) := by
        simp only [lsubst, liftLSubstVars, packedLookupRegion_rename]
        change Region.let₂ (.var 0) ((packedLookupRegion 0 i : Region Φ).substVars
          (Tm.singleSubst (.var 1))) = _
        rw [packedLookupRegion_subst 0 i 1 (Tm.singleSubst (.var 1)) rfl]
        rfl
      change CfgEta.Eqv [_] _ (packedLookupRegion 0 (i + 1)) [A]
      rw [eq]
      exact .native (.base (.refl (packedLookupRegion_typed (Γ := B :: Γ) (i := i + 1) hi rfl).hasType))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.Reification

open CfgEta CfgEta.TypeCategory CfgEta.TypeCategory.ConstructorReification Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (J : V ⥤ TypeCategory Φ ([] : VCtx τ)) (M : TypeModel τ V)
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) (Γ := []) A)
  {X A B : τ}

theorem mapTypeHom_id :
    mapTypeHom J M objIso (𝟙 (M.obj X)) = 𝟙 (ofType X) := by
  simp [mapTypeHom]

theorem mapTypeHom_comp (f : M.obj X ⟶ M.obj A) (g : M.obj A ⟶ M.obj B) :
    mapTypeHom J M objIso (f ≫ g) = mapTypeHom J M objIso f ≫ mapTypeHom J M objIso g := by
  simp [mapTypeHom]

set_option backward.isDefEq.respectTransparency false in
theorem mapPackedLookup
    (hFst : ∀ A B : τ, mapTypeHom J M objIso
      ((M.productIso A B).hom ≫ fst (M.obj A) (M.obj B)) = productFst A B)
    (hSnd : ∀ A B : τ, mapTypeHom J M objIso
      ((M.productIso A B).hom ≫ snd (M.obj A) (M.obj B)) = productSnd A B)
    (Γ : VCtx τ) (i : Nat) (hi : At Γ i A) :
    mapTypeHom J M objIso ((inputRecordIso M Γ).inv ≫ lookup M i hi) = packedLookup Γ i hi := by
  induction Γ generalizing i with
  | nil => simp [At] at hi
  | cons B Γ ih =>
    cases i with
    | zero =>
      cases Option.some.inj hi
      change mapTypeHom J M objIso
        ((inputRecordIso M (A :: Γ)).inv ≫ snd (ctxObj M Γ) (M.obj A)) =
        productSnd (packedInputType Γ) A
      simpa only [inputRecordIso, Iso.trans_inv, Iso.symm_inv, whiskerRightIso_inv,
        Category.assoc, whiskerRight_snd] using hSnd (packedInputType Γ) A
    | succ i =>
      change mapTypeHom J M objIso ((inputRecordIso M (B :: Γ)).inv ≫
        fst (ctxObj M Γ) (M.obj B) ≫ lookup M i hi) = _
      simp only [inputRecordIso, Iso.trans_inv, Iso.symm_inv, whiskerRightIso_inv,
        Category.assoc, whiskerRight_fst_assoc, packedLookup]
      rw [← Category.assoc (M.productIso (packedInputType Γ) B).hom,
        mapTypeHom_comp, hFst, ih i hi]

section Constructors

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

theorem branchArrow_pure {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    PureReturn pe (branchArrow ha) := by
  have hp : Tm.Pure pe a := by induction ha <;> constructor <;> assumption
  rw [branchArrow_eq_return]
  exact pureReturn_ofRegion pe ha.hasType hp

variable {J M objIso}

theorem mapTypeHom_pair (cmp : ConstructorComparisons J M objIso)
    (productLaws : ProductProjectionLaws (τ := τ) (Φ := Φ) pe)
    (imagePure : ∀ {X A : τ} (f : M.obj X ⟶ M.obj A), PureReturn pe (mapTypeHom J M objIso f))
    {a b : Tm Φ} (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B)
    {f : M.obj X ⟶ M.obj A} {g : M.obj X ⟶ M.obj B}
    (hf : mapTypeHom J M objIso f = branchArrow ha)
    (hg : mapTypeHom J M objIso g = branchArrow hb) :
    mapTypeHom J M objIso (lift f g ≫ (M.productIso A B).inv) = branchArrow (.pair ha hb) := by
  refine productLaws.hom_ext (imagePure _) (branchArrow_pure pe (.pair ha hb)) ?_ ?_
  · rw [branchArrow_pair_fst ha hb (productLaws.fst ha hb), ← cmp.fst, ← mapTypeHom_comp, ← hf]
    congr 1
    simp only [fstMap, Category.assoc, Iso.inv_hom_id_assoc, lift_fst]
  · rw [branchArrow_pair_snd ha hb (productLaws.snd ha hb), ← cmp.snd, ← mapTypeHom_comp, ← hg]
    congr 1
    simp only [sndMap, Category.assoc, Iso.inv_hom_id_assoc, lift_snd]

end Constructors

section Denotation

variable [SymmetricCategory V]
  [PremonoidalCategory (TypeCategory Φ ([] : VCtx τ))] [SymmetricPremonoidalCategory (TypeCategory Φ ([] : VCtx τ))]
  [HasFiniteCoproducts (TypeCategory Φ ([] : VCtx τ))]
  [DistributiveTensor V] [DistributivePremonoidalCategory (TypeCategory Φ ([] : VCtx τ))]
  [DistributiveFreydCategory J] [InstructionModel J M Φ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem singleton_lookup (hi : At [X] 0 X) :
    lookup M 0 hi = (λ_ (M.obj X)).hom := by
  rw [leftUnitor_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem compare_packedInputProjection
    (hFst : ∀ A B : τ, mapTypeHom J M objIso (fstMap M A B) = productFst A B)
    (hSnd : ∀ A B : τ, mapTypeHom J M objIso (sndMap M A B) = productSnd A B)
    {Γ : VCtx τ} {i : Nat} (hi : At Γ i A) :
    let X := packedInputType Γ
    ∃ p : ctxObj M [X] ⟶ M.obj A,
      Denotes J M (packedInputProjection_hasType hi
        (.var rfl : Tm.HasType [X] (.var 0 : Tm Φ) X)) (J.map p) ∧
      mapTypeHom J M objIso (((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫ p) =
        ofRegion (packedLookupRegion_typed (Φ := Φ) hi (show At [X] 0 X from rfl)) := by
  let X := packedInputType Γ
  have d := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At [X] 0 X)
  refine ⟨_, packedInputProjection_denotes J M hi d, ?_⟩
  rw [singleton_lookup M (rfl : At [X] 0 X), Iso.inv_hom_id_assoc, mapPackedLookup J M objIso hFst hSnd,
    packedLookup_eq_ofRegion]

set_option backward.isDefEq.respectTransparency false in
theorem compare_unit
    (hUnit : mapTypeHom J M objIso (unitMap M X) =
      branchArrow (.unit : Tm.BranchValue [X] (.unit : Tm Φ) Silmaril.unit)) :
    ∃ p : ctxObj M [X] ⟶ M.obj (Silmaril.unit : τ),
      Denotes J M (.unit : Tm.HasType [X] (.unit : Tm Φ) Silmaril.unit) (J.map p) ∧
      mapTypeHom J M objIso (((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫ p) =
        ofRegion (returnRegion_typed (.unit : Tm.HasType [X] (.unit : Tm Φ) Silmaril.unit)) := by
  refine ⟨toUnit _ ≫ M.unitIso.inv, .unit, ?_⟩
  rw [← branchArrow_eq_return (.unit : Tm.BranchValue [X] (.unit : Tm Φ) Silmaril.unit),
    ← Category.assoc,
    show ((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫ toUnit (ctxObj M [X]) =
      toUnit (M.obj X) from toUnit_unique _ _]
  exact hUnit

set_option backward.isDefEq.respectTransparency false in
theorem compare_constructor (cmp : ConstructorComparisons J M objIso)
    (productLaws : ProductProjectionLaws (τ := τ) (Φ := Φ) pe)
    (imagePure : ∀ {X A : τ} (f : M.obj X ⟶ M.obj A), PureReturn pe (mapTypeHom J M objIso f))
    {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    ∃ p : ctxObj M [X] ⟶ M.obj A, Denotes J M ha.hasType (J.map p) ∧
      mapTypeHom J M objIso (((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫ p) =
        ofRegion (returnRegion_typed ha.hasType) := by
  rw [← branchArrow_eq_return ha]
  induction ha with
  | @var i A h =>
    cases i with
    | zero =>
      have e : X = A := Option.some.inj h
      subst A
      refine ⟨lookup M 0 h, Denotes.var h, ?_⟩
      rw [singleton_lookup M h, Iso.inv_hom_id, mapTypeHom_id, branchArrow_var]
    | succ i => simp [At] at h
  | unit =>
    simpa only [← branchArrow_eq_return (.unit : Tm.BranchValue [X] (.unit : Tm Φ) Silmaril.unit)]
      using compare_unit J M objIso (cmp.unit X)
  | @pair a A b B ha hb iha ihb =>
    obtain ⟨f, df, hf⟩ := iha
    obtain ⟨g, dg, hg⟩ := ihb
    refine ⟨lift f g ≫ (M.productIso A B).inv, ?_, ?_⟩
    · simpa only [Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.pair_map, ← J.map_comp] using
        (Denotes.pair df dg)
    · rw [← Category.assoc, comp_lift]
      exact mapTypeHom_pair pe cmp productLaws imagePure ha hb hf hg
  | @inl a A B ha iha =>
    obtain ⟨f, df, hf⟩ := iha
    refine ⟨f ≫ inlMap M A B, ?_, ?_⟩
    · simpa only [inlMap, J.map_comp] using (Denotes.inl (B := B) df)
    · rw [← Category.assoc, mapTypeHom_comp, hf, cmp.inl, branchArrow_inl]
  | @inr b B A hb ihb =>
    obtain ⟨g, dg, hg⟩ := ihb
    refine ⟨g ≫ inrMap M A B, ?_, ?_⟩
    · simpa only [inrMap, J.map_comp] using (Denotes.inr (A := A) dg)
    · rw [← Category.assoc, mapTypeHom_comp, hg, cmp.inr, branchArrow_inr]

end Denotation

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.Reification
