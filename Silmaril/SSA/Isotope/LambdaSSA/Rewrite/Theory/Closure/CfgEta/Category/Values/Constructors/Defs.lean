module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Categorical.Defs

/-! # Constructor arrows and their model comparisons -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open Silmaril
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

variable {X A B D : τ} {a b : Tm Φ} {r s : Region Φ}

/-- The literal branch representative of a constructor value. -/
def branchArrow (ha : Tm.BranchValue [X] a A) : ofType (Φ := Φ) (Γ := []) X ⟶ ofType A :=
  ofRegion (.br rfl ha : ValueBranches [X] (.br 0 a) [A])

theorem productFstBranches (A B : τ) :
    ValueBranches [Silmaril.product A B] (.let₂ (.var 0) (.br 0 (.var 1)) : Region Φ) [A] :=
  .let₂ (.var (i := 0) rfl) (.br rfl (.var (i := 1) rfl))

theorem productSndBranches (A B : τ) :
    ValueBranches [Silmaril.product A B] (.let₂ (.var 0) (.br 0 (.var 0)) : Region Φ) [B] :=
  .let₂ (.var (i := 0) rfl) (.br rfl (.var (i := 0) rfl))

def productFst (A B : τ) :
    ofType (Φ := Φ) (Γ := []) (Silmaril.product A B) ⟶ ofType A :=
  ofRegion (productFstBranches A B)

def productSnd (A B : τ) :
    ofType (Φ := Φ) (Γ := []) (Silmaril.product A B) ⟶ ofType B :=
  ofRegion (productSndBranches A B)

/-- The path of product projections through the packed input record. -/
def packedLookup : (Γ : VCtx τ) → (i : Nat) → {A : τ} → At Γ i A →
    (ofType (Φ := Φ) (Γ := []) (packedInputType Γ) ⟶ ofType A)
  | [], _, _, h => by simp [At] at h
  | B :: Γ, 0, A, h => by
      cases Option.some.inj h
      exact productSnd (packedInputType Γ) B
  | B :: Γ, i + 1, _, h => productFst (packedInputType Γ) B ≫ packedLookup Γ i h

/-- Read the requested record field, using slot one for the tail
after each product binder. -/
def packedLookupRegion : Nat → Nat → Region Φ
  | j, 0 => .let₂ (.var j) (.br 0 (.var 0))
  | j, i + 1 => .let₂ (.var j) (packedLookupRegion 1 i)

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification

open CfgEta.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (J : V ⥤ TypeCategory Φ ([] : VCtx τ)) (M : TypeModel τ V)
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) (Γ := []) A)
  {X A B : τ}

/-- Interpret a value arrow and transport its endpoints to the exact syntax types. -/
def mapTypeHom (f : M.obj X ⟶ M.obj A) : ofType (Φ := Φ) (Γ := []) X ⟶ ofType A :=
  (objIso X).inv ≫ J.map f ≫ (objIso A).hom

section Constructors

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

def unitMap (X : τ) : M.obj X ⟶ M.obj (Silmaril.unit : τ) :=
  toUnit _ ≫ M.unitIso.inv

def fstMap (A B : τ) : M.obj (Silmaril.product A B) ⟶ M.obj A :=
  (M.productIso A B).hom ≫ fst _ _

def sndMap (A B : τ) : M.obj (Silmaril.product A B) ⟶ M.obj B :=
  (M.productIso A B).hom ≫ snd _ _

noncomputable def inlMap (A B : τ) : M.obj A ⟶ M.obj (Silmaril.coprod A B) :=
  coprod.inl ≫ (M.coprodIso A B).inv

noncomputable def inrMap (A B : τ) : M.obj B ⟶ M.obj (Silmaril.coprod A B) :=
  coprod.inr ≫ (M.coprodIso A B).inv

/-- Agreement on the primitive unit, projection, and injection arrows. -/
structure ConstructorComparisons : Prop where
  unit (X : τ) : mapTypeHom J M objIso (unitMap M X) =
    branchArrow (.unit : Tm.BranchValue [X] (.unit : Tm Φ) Silmaril.unit)
  fst (A B : τ) : mapTypeHom J M objIso (fstMap M A B) = productFst A B
  snd (A B : τ) : mapTypeHom J M objIso (sndMap M A B) = productSnd A B
  inl (A B : τ) : mapTypeHom J M objIso (inlMap M A B) =
    (sumCofan (Φ := Φ) (Γ := []) A B).inl
  inr (A B : τ) : mapTypeHom J M objIso (inrMap M A B) =
    (sumCofan (Φ := Φ) (Γ := []) A B).inr

/-- The two constructor projection reductions and product extensionality among pure arrows. -/
structure ProductProjectionLaws : Prop where
  fst {X A B : τ} {a b : Tm Φ} (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    CfgEta.Eqv [X] (.let₂ (.pair a b) (.br 0 (.var 1))) (.br 0 a) [A]
  snd {X A B : τ} {a b : Tm Φ} (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    CfgEta.Eqv [X] (.let₂ (.pair a b) (.br 0 (.var 0))) (.br 0 b) [B]
  hom_ext {X A B : τ}
    {f g : ofType (Φ := Φ) (Γ := []) X ⟶ ofType (Silmaril.product A B)} :
    PureReturn pe f → PureReturn pe g →
    f ≫ productFst A B = g ≫ productFst A B →
    f ≫ productSnd A B = g ≫ productSnd A B → f = g

end Constructors

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification
