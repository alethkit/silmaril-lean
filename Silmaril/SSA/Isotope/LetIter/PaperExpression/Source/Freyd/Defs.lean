module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Hom.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Categorical.Defs

/-! # Compare fixed-effect expression homs with a distributive Freyd interpretation -/

@[expose] public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Semantics.Categorical (TypeModel InstructionModel)

variable {τ : Type u} {Φ : Type v} {ε : Type w} [TypeFormers τ]
  [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) (M : TypeModel τ V) [DistributiveFreydCategory J]

/-- Computation arrows between the interpretations of source type codes. -/
abbrev Arrow (X A : τ) := J.obj (M.obj X) ⟶ J.obj (M.obj A)

local notation "semanticBind" =>
  Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "semanticPair" =>
  Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair
local notation "semanticCase" =>
  Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.caseWithContext

/-- Pure slot lookup on the interpretation of the source's packed type. -/
noncomputable def projection : (Γ : EffectCtx τ ε) → (i : Fin Γ.length) →
    (M.obj (packType Γ) ⟶ M.obj (Γ.get i).1)
  | [], i => i.elim0
  | (A, _) :: Γ, i => Fin.cases
      ((M.productIso (packType Γ) A).hom ≫ CartesianMonoidalCategory.snd _ _)
      (fun j => (M.productIso (packType Γ) A).hom ≫
        CartesianMonoidalCategory.fst _ _ ≫ projection Γ j) i

noncomputable def applyInstruction [InstructionModel J M Φ] {X : τ} (f : Φ)
    (a : Arrow J M X (instrSrc f)) : Arrow J M X (instrTrg f) :=
  a ≫ InstructionModel.denote f

noncomputable def toUnit {X : τ} : Arrow J M X unit :=
  J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv)

noncomputable def pair {X A B : τ} (a : Arrow J M X A) (b : Arrow J M X B) :
    Arrow J M X (product A B) :=
  semanticPair J a b ≫ J.map (M.productIso A B).inv

noncomputable def bind {X A B : τ} (a : Arrow J M X A) (b : Arrow J M (product X A) B) :
    Arrow J M X B :=
  semanticBind J a (J.map (M.productIso X A).inv ≫ b)

/-- Expose the product initializer and form the source's left-associated
two-slot extension of the retained input. -/
def pairExtension (X A B : τ) :
    M.obj X ⊗ M.obj (product A B) ⟶ M.obj (product (product X A) B) :=
  (M.obj X ◁ (M.productIso A B).hom) ≫
    (α_ (M.obj X) (M.obj A) (M.obj B)).inv ≫
    ((M.productIso X A).inv ▷ M.obj B) ≫ (M.productIso (product X A) B).inv

noncomputable def bindPair {X A B D : τ} (a : Arrow J M X (product A B))
    (b : Arrow J M (product (product X A) B) D) : Arrow J M X D :=
  semanticBind J a (J.map (pairExtension M X A B) ≫ b)

noncomputable def inl {X A B : τ} (a : Arrow J M X A) : Arrow J M X (coprod A B) :=
  a ≫ J.map (coprod.inl ≫ (M.coprodIso A B).inv)

noncomputable def inr {X A B : τ} (b : Arrow J M X B) : Arrow J M X (coprod A B) :=
  b ≫ J.map (coprod.inr ≫ (M.coprodIso A B).inv)

noncomputable def caseWithContext {X A B D : τ} (a : Arrow J M X (coprod A B))
    (l : Arrow J M (product X A) D) (r : Arrow J M (product X B) D) : Arrow J M X D :=
  semanticCase J (a ≫ J.map (M.coprodIso A B).hom)
    (J.map (M.productIso X A).inv ≫ l) (J.map (M.productIso X B).inv ≫ r)

noncomputable def abort {X A : τ} (a : Arrow J M X empty) : Arrow J M X A :=
  a ≫ J.map (M.emptyIsInitial.to (M.obj A))

variable [InstructionModel J M Φ]

/-- Interpretation by the Freyd operations on the packed type. The graph
carries the source judgment, including a common effect bound for all
computations. -/
inductive Denotes (e : ε) :
    (Γ : EffectCtx τ ε) → (A : τ) → Expr Φ → Arrow J M (packType Γ) A → Prop where
  | var {Γ} (i : Fin Γ.length) : (Γ.get i).2 ≤ e →
      Denotes e Γ (Γ.get i).1 (.var i.val) (J.map (projection M Γ i))
  | op {Γ f a v} : instrEff f ≤ e → Denotes e Γ (instrSrc f) a v →
      Denotes e Γ (instrTrg f) (.op f a) (applyInstruction J M f v)
  | let1 {Γ A B a b v w} : Denotes e Γ A a v → Denotes e ((A, ⊥) :: Γ) B b w →
      Denotes e Γ B (.let₁ a b) (bind J M v w)
  | pair {Γ A B a b v w} : Denotes e Γ A a v → Denotes e Γ B b w →
      Denotes e Γ (product A B) (.pair a b) (pair J M v w)
  | unit (Γ) : Denotes e Γ Silmaril.unit .unit (toUnit J M)
  | let2 {Γ A B D a b v w} : Denotes e Γ (product A B) a v →
      Denotes e ((B, ⊥) :: (A, ⊥) :: Γ) D b w →
      Denotes e Γ D (.let₂ a b) (bindPair J M v w)
  | inl {Γ A B a v} : Denotes e Γ A a v →
      Denotes e Γ (coprod A B) (.inl a) (inl J M v)
  | inr {Γ A B a v} : Denotes e Γ B a v →
      Denotes e Γ (coprod A B) (.inr a) (inr J M v)
  | case {Γ A B D a l r v w z} : Denotes e Γ (coprod A B) a v →
      Denotes e ((A, ⊥) :: Γ) D l w → Denotes e ((B, ⊥) :: Γ) D r z →
      Denotes e Γ D (.case a l r) (caseWithContext J M v w z)
  | abort {Γ A a v} : Denotes e Γ empty a v →
      Denotes e Γ A (.abort a) (abort J M v)

/-- A map from the source homs at e preserving the operations used in
expression interpretation. The target uses the supplied Freyd structure
and the chosen type comparisons. -/
structure Comparison (Φ : Type v) [HasTy Φ τ] [HasEff Φ ε] [InstructionModel J M Φ]
    (e : ε) where
  map : ∀ {X A : τ}, Hom Φ X A e → Arrow J M X A
  map_projection (Γ : EffectCtx τ ε) (i : Fin Γ.length) :
    map (Hom.projection Γ i) = J.map (projection M Γ i)
  map_instruction {X : τ} {f : Φ} (h : instrEff f ≤ e) (a : Hom Φ X (instrSrc f) e) :
    map (Hom.applyInstruction h a) = applyInstruction J M f (map a)
  map_unit (X : τ) : map (Hom.toUnit (X := X)) = toUnit J M
  map_pair {X A B : τ} (a : Hom Φ X A e) (b : Hom Φ X B e) :
    map (Hom.pair a b) = pair J M (map a) (map b)
  map_bind {X A B : τ} (a : Hom Φ X A e) (b : Hom Φ (product X A) B e) :
    map (Hom.bind a b) = bind J M (map a) (map b)
  map_bindPair {X A B D : τ} (a : Hom Φ X (product A B) e)
      (b : Hom Φ (product (product X A) B) D e) :
    map (Hom.bindPair a b) = bindPair J M (map a) (map b)
  map_inl {X A B : τ} (a : Hom Φ X A e) :
    map (Hom.inl (B := B) a) = inl J M (map a)
  map_inr {X A B : τ} (b : Hom Φ X B e) :
    map (Hom.inr (A := A) b) = inr J M (map b)
  map_case {X A B D : τ} (a : Hom Φ X (coprod A B) e)
      (l : Hom Φ (product X A) D e) (r : Hom Φ (product X B) D e) :
    map (Hom.caseWithContext a l r) = caseWithContext J M (map a) (map l) (map r)
  map_abort {X A : τ} (a : Hom Φ X empty e) :
    map (Hom.abort (A := A) a) = abort J M (map a)

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd
