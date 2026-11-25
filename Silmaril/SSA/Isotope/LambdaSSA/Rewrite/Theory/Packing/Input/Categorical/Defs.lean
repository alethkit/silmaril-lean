module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # The value-category isomorphism for packed inputs -/

@[expose] public section

universe v u w

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Region (packedInputType)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

variable {V : Type u} [Category.{v} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type w} [TypeFormers τ] (M : TypeModel τ V)

/-- The environment product and its corresponding object-language record. -/
def inputRecordIso : (Γ : VCtx τ) → ctxObj M Γ ≅ M.obj (packedInputType Γ)
  | [] => M.unitIso.symm
  | A :: Γ => MonoidalCategory.whiskerRightIso (inputRecordIso Γ) (M.obj A) ≪≫
      (M.productIso (packedInputType Γ) A).symm

/-- Reindex the environment as a context containing just the packed record. -/
def packedInputIso (Γ : VCtx τ) : ctxObj M Γ ≅ ctxObj M [packedInputType Γ] :=
  inputRecordIso M Γ ≪≫ (λ_ (M.obj (packedInputType Γ))).symm

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
