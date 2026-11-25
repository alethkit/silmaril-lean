module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms

/-! # Loop-free LetIter denotation in distributive Freyd categories -/

@[expose] public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression

open LocallyNameless (Tm Derivation)
open Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind pair caseWithContext)

variable {τ : Type u} {Φ : Type v} {ν : Type w}

/-- A native term uses only the loop-free expression constructors. -/
def LoopFree : {n : Nat} → Tm ν Φ n → Prop
  | _, .fv _ | _, .bv _ | _, .unit => True
  | _, .op _ a | _, .inl a | _, .inr a | _, .abort a => LoopFree a
  | _, .let₁ a b | _, .pair a b | _, .let₂ a b => LoopFree a ∧ LoopFree b
  | _, .case a l r => LoopFree a ∧ LoopFree l ∧ LoopFree r
  | _, .iter _ _ => False

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)
  [DecidableEq ν] [TypeFormers τ] (M : TypeModel τ V)
  [HasTy Φ τ] [InstructionModel J M Φ]

/-- The native expression denotation can be evaluated in a distributive
Freyd category using only its chosen non-iterative operations. -/
noncomputable def denoteLoopFree [DistributiveFreydCategory J] :
    {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
      Derivation Φ Γ β t A → LoopFree t → (J.obj (envObj M Γ β) ⟶ J.obj (M.obj A))
  | _, _, _, _, _, .fv h, _ => J.map (freeLookup M _ h)
  | _, _, _, _, _, .bv, _ => J.map (boundVar M _)
  | _, _, _, _, _, .op a, h => denoteLoopFree a h ≫ InstructionModel.denote _
  | Γ, _, β, _, _, .let₁ a b, h => bind J (denoteLoopFree a h.1) <|
      J.map (envSnocIso M Γ β _).hom ≫ denoteLoopFree b h.2
  | _, _, _, _, _, .unit, _ => J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv)
  | _, _, _, _, _, .pair a b, h =>
      pair J (denoteLoopFree a h.1) (denoteLoopFree b h.2) ≫ J.map (M.productIso _ _).inv
  | Γ, _, β, _, _, .let₂ a b, h => bind J (denoteLoopFree a h.1) <|
      J.map ((𝟙 _) ⊗ₘ (M.productIso _ _).hom) ≫
        J.map (envPairHom M Γ β _ _) ≫ denoteLoopFree b h.2
  | _, _, _, _, _, .inl a, h =>
      denoteLoopFree a h ≫ J.map (coprod.inl ≫ (M.coprodIso _ _).inv)
  | _, _, _, _, _, .inr b, h =>
      denoteLoopFree b h ≫ J.map (coprod.inr ≫ (M.coprodIso _ _).inv)
  | Γ, _, β, _, _, .case a l r, h =>
      caseWithContext J (denoteLoopFree a h.1 ≫ J.map (M.coprodIso _ _).hom)
        (J.map (envSnocIso M Γ β _).hom ≫ denoteLoopFree l h.2.1)
        (J.map (envSnocIso M Γ β _).hom ≫ denoteLoopFree r h.2.2)
  | _, _, _, _, _, .abort a, h =>
      denoteLoopFree a h ≫ J.map (M.emptyIsInitial.to (M.obj _))
  | _, _, _, _, _, .iter _ _, h => False.elim h

/-- Interpret an all-bound expression on the product of its bound slots.
The left unitor removes the empty free-context factor. -/
noncomputable def denoteBoundLoopFree [DistributiveFreydCategory J]
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A) (h : LoopFree t) :
    J.obj (boundObj M β) ⟶ J.obj (M.obj A) :=
  J.map (λ_ (boundObj M β)).inv ≫ denoteLoopFree J M d h

end Silmaril.Isotope.LetIter.PaperExpression
