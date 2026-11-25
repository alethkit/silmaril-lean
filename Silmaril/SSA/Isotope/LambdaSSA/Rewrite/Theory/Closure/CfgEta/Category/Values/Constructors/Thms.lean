module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues

/-! # Reification of packed lookups and constructor value returns -/

public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

open CfgEta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

variable {X A B D : τ} {a b : Tm Φ} {r s : Region Φ}

/-- A constructor value returned by the term translation gives the same arrow as its literal branch. -/
theorem branchArrow_eq_return (ha : Tm.BranchValue [X] a A) :
    branchArrow ha = ofRegion (returnRegion_typed ha.hasType) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.branchArrow_eq_return ha

theorem branchArrow_var : branchArrow (.var (i := 0) (rfl : At [X] 0 X) :
    Tm.BranchValue [X] (.var 0 : Tm Φ) X) = 𝟙 (ofType X) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.branchArrow_var

/-- Composition of singleton representatives is literal label substitution with weakened capture. -/
theorem ofRegion_comp (hr : ValueBranches [X] r [A]) (hs : ValueBranches [A] s [B]) :
    ofRegion hr ≫ ofRegion hs = ofRegion (seqValueBranches hr hs) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.ofRegion_comp hr hs

theorem branchArrow_inl (ha : Tm.BranchValue [X] a A) (B : τ) :
    branchArrow ha ≫ (sumCofan (Φ := Φ) (Γ := []) A B).inl =
      branchArrow (.inl (B := B) ha) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.branchArrow_inl ha B

theorem branchArrow_inr (B : τ) (ha : Tm.BranchValue [X] a A) :
    branchArrow ha ≫ (sumCofan (Φ := Φ) (Γ := []) B A).inr =
      branchArrow (.inr (A := B) ha) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.branchArrow_inr B ha

/-- Constructor-pair β contracts the syntactic left projection in the opt-in relation. -/
theorem branchPair_fst_beta (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    ProductBeta.Eqv [X] (.let₂ (.pair a b) (.br 0 (.var 1))) (.br 0 a) [A] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.branchPair_fst_beta ha hb

/-- Constructor-pair β contracts the syntactic right projection in the opt-in relation. -/
theorem branchPair_snd_beta (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    ProductBeta.Eqv [X] (.let₂ (.pair a b) (.br 0 (.var 0))) (.br 0 b) [B] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.branchPair_snd_beta ha hb

theorem branchArrow_pair_fst
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B)
    (h : Eqv [X] (.let₂ (.pair a b) (.br 0 (.var 1))) (.br 0 a) [A]) :
    branchArrow (.pair ha hb) ≫ productFst A B = branchArrow ha :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.branchArrow_pair_fst ha hb h

theorem branchArrow_pair_snd
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B)
    (h : Eqv [X] (.let₂ (.pair a b) (.br 0 (.var 0))) (.br 0 b) [B]) :
    branchArrow (.pair ha hb) ≫ productSnd A B = branchArrow hb :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.branchArrow_pair_snd ha hb h

theorem packedLookupRegion_typed {Γ Δ : VCtx τ} {i j : Nat} (hi : At Γ i A)
    (hj : At Δ j (packedInputType Γ)) :
    ValueBranches Δ (packedLookupRegion j i : Region Φ) [A] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.packedLookupRegion_typed hi hj


/-- The composite of projections is represented by the literal nested product decoder. -/
theorem packedLookup_eq_ofRegion (Γ : VCtx τ) (i : Nat) (hi : At Γ i A) :
    packedLookup (Φ := Φ) Γ i hi =
      ofRegion (packedLookupRegion_typed (Φ := Φ) hi (show At [packedInputType Γ] 0 _ from rfl)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.packedLookup_eq_ofRegion Γ i hi

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification

open CfgEta CfgEta.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (J : V ⥤ TypeCategory Φ ([] : VCtx τ)) (M : TypeModel τ V)
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) (Γ := []) A)
  {X A B : τ}

@[simp] theorem mapTypeHom_id :
    mapTypeHom J M objIso (𝟙 (M.obj X)) = 𝟙 (ofType X) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.Reification.mapTypeHom_id J M objIso

theorem mapTypeHom_comp (f : M.obj X ⟶ M.obj A) (g : M.obj A ⟶ M.obj B) :
    mapTypeHom J M objIso (f ≫ g) = mapTypeHom J M objIso f ≫ mapTypeHom J M objIso g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.Reification.mapTypeHom_comp J M objIso f g

/-- Preserving the two immediate projections suffices to compare every packed context lookup. -/
theorem mapPackedLookup
    (hFst : ∀ A B : τ, mapTypeHom J M objIso
      ((M.productIso A B).hom ≫ fst (M.obj A) (M.obj B)) = productFst A B)
    (hSnd : ∀ A B : τ, mapTypeHom J M objIso
      ((M.productIso A B).hom ≫ snd (M.obj A) (M.obj B)) = productSnd A B)
    (Γ : VCtx τ) (i : Nat) (hi : At Γ i A) :
    mapTypeHom J M objIso ((inputRecordIso M Γ).inv ≫ lookup M i hi) = packedLookup Γ i hi :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.Reification.mapPackedLookup J M objIso hFst hSnd Γ i hi

section Constructors

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

theorem branchArrow_pure {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    PureReturn pe (branchArrow ha) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.Reification.branchArrow_pure pe ha

variable {J M objIso}

/-- Projection β and pure extensionality identify the transported Cartesian pairing with a syntactic pair. -/
theorem mapTypeHom_pair (cmp : ConstructorComparisons J M objIso)
    (productLaws : ProductProjectionLaws (τ := τ) (Φ := Φ) pe)
    (imagePure : ∀ {X A : τ} (f : M.obj X ⟶ M.obj A), PureReturn pe (mapTypeHom J M objIso f))
    {a b : Tm Φ} (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B)
    {f : M.obj X ⟶ M.obj A} {g : M.obj X ⟶ M.obj B}
    (hf : mapTypeHom J M objIso f = branchArrow ha)
    (hg : mapTypeHom J M objIso g = branchArrow hb) :
    mapTypeHom J M objIso (lift f g ≫ (M.productIso A B).inv) = branchArrow (.pair ha hb) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.Reification.mapTypeHom_pair pe cmp productLaws imagePure ha hb hf hg

end Constructors

section Denotation

variable [SymmetricCategory V]
  [PremonoidalCategory (TypeCategory Φ ([] : VCtx τ))] [SymmetricPremonoidalCategory (TypeCategory Φ ([] : VCtx τ))]
  [HasFiniteCoproducts (TypeCategory Φ ([] : VCtx τ))]
  [DistributiveTensor V] [DistributivePremonoidalCategory (TypeCategory Φ ([] : VCtx τ))]
  [DistributiveFreydCategory J] [InstructionModel J M Φ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The packed projection term denotes the syntactic nested product decoder after transport. -/
theorem compare_packedInputProjection
    (hFst : ∀ A B : τ, mapTypeHom J M objIso (fstMap M A B) = productFst A B)
    (hSnd : ∀ A B : τ, mapTypeHom J M objIso (sndMap M A B) = productSnd A B)
    {Γ : VCtx τ} {i : Nat} (hi : At Γ i A) :
    let X := packedInputType Γ
    ∃ p : ctxObj M [X] ⟶ M.obj A,
      Denotes J M (packedInputProjection_hasType hi
        (.var rfl : Tm.HasType [X] (.var 0 : Tm Φ) X)) (J.map p) ∧
      mapTypeHom J M objIso (((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫ p) =
        ofRegion (packedLookupRegion_typed (Φ := Φ) hi (show At [X] 0 X from rfl)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.Reification.compare_packedInputProjection J M objIso hFst hSnd hi

/-- A unit return needs only agreement on the unit arrow at its domain. -/
theorem compare_unit
    (hUnit : mapTypeHom J M objIso (unitMap M X) =
      branchArrow (.unit : Tm.BranchValue [X] (.unit : Tm Φ) Silmaril.unit)) :
    ∃ p : ctxObj M [X] ⟶ M.obj (Silmaril.unit : τ),
      Denotes J M (.unit : Tm.HasType [X] (.unit : Tm Φ) Silmaril.unit) (J.map p) ∧
      mapTypeHom J M objIso (((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫ p) =
        ofRegion (returnRegion_typed (.unit : Tm.HasType [X] (.unit : Tm Φ) Silmaril.unit)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.Reification.compare_unit
    J M objIso hUnit

/-- Every singleton constructor value has a pure graph arrow that agrees with its syntactic return. -/
theorem compare_constructor (cmp : ConstructorComparisons J M objIso)
    (productLaws : ProductProjectionLaws (τ := τ) (Φ := Φ) pe)
    (imagePure : ∀ {X A : τ} (f : M.obj X ⟶ M.obj A), PureReturn pe (mapTypeHom J M objIso f))
    {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    ∃ p : ctxObj M [X] ⟶ M.obj A, Denotes J M ha.hasType (J.map p) ∧
      mapTypeHom J M objIso (((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫ p) =
        ofRegion (returnRegion_typed ha.hasType) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ConstructorValues.Reification.compare_constructor J M objIso pe cmp productLaws imagePure ha

end Denotation

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification
