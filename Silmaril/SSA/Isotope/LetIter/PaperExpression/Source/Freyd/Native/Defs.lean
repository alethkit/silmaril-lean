module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Categorical.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Thms

/-! # Native loop-free representatives of the source Freyd interpretation -/

@[expose] public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open LocallyNameless (Tm Derivation)
open Semantics.Categorical (TypeModel InstructionModel boundObj envObj)

variable {τ : Type u} {Φ : Type v} {ε : Type w} [TypeFormers τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]

/-- Compare interpretation of the source's packed type with the native
product of bound variables, using the model's chosen type comparisons. -/
def packedTypeIso (M : TypeModel τ V) :
    (Γ : EffectCtx τ ε) → M.obj (packType Γ) ≅ boundObj M Γ.toBoundCtx
  | [] => M.unitIso
  | (A, _) :: Γ => M.productIso (packType Γ) A ≪≫
      (packedTypeIso M Γ ⊗ᵢ Iso.refl (M.obj A))

/-- Add the unit from the empty free context to the packed input. -/
def packedEnvIso (M : TypeModel τ V) (Γ : EffectCtx τ ε) :
    M.obj (packType Γ) ≅ envObj M (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx :=
  packedTypeIso M Γ ≪≫ (λ_ (boundObj M Γ.toBoundCtx)).symm

variable [HasTy Φ τ]

/-- The result of lowering a source expression together with its exact
native derivation. -/
structure Lowering (Γ : EffectCtx τ ε) (a : Expr Φ) (A : τ) where
  term : Tm Empty Φ Γ.length
  lowered : a.toLetIter Γ.length = some term
  typed : Derivation Φ (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx term A

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) (M : TypeModel τ V) [DistributiveFreydCategory J] [InstructionModel J M Φ]

/-- Interpret a lowered representative on the original packed source type. -/
noncomputable def Lowering.denote {Γ : EffectCtx τ ε} {a : Expr Φ} {A : τ}
    (d : Lowering Γ a A) : Arrow J M (packType Γ) A :=
  J.map (packedEnvIso M Γ).hom ≫ denoteLoopFree J M d.typed (loopFree_of_lowering d.lowered)

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native
