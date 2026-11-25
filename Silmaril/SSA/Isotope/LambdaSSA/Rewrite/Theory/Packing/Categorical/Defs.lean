module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Defs

/-! # Value arrows for the packed exit interface -/

@[expose] public section

universe v u w

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Silmaril.Isotope.LambdaSSA.Region (packedExitType)

variable {V : Type u} [Category.{v} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type w} [TypeFormers τ] (M : TypeModel τ V)

/-- Insert a typed label payload into the right-associated packed sum. -/
noncomputable def packedLabelInject : {L : LCtx τ} → (i : Nat) → {A : τ} →
    At L i A → (M.obj A ⟶ M.obj (packedExitType L))
  | [], _, _, h => by simp [At] at h
  | B :: L, 0, A, h =>
      eqToHom (congrArg M.obj (Option.some.inj h).symm) ≫ coprod.inl ≫ (M.coprodIso B (packedExitType L)).inv
  | B :: L, i + 1, _, h =>
      packedLabelInject i h ≫ coprod.inr ≫ (M.coprodIso B (packedExitType L)).inv

/-- Encode the finite categorical coproduct as the interpreted packed type. -/
noncomputable def packLabel (L : LCtx τ) : labelObj M L ⟶ M.obj (packedExitType L) :=
  Sigma.desc fun i => packedLabelInject M i (labelAt_get L i)

/-- Decode a packed type into the categorical coproduct of the original labels. -/
noncomputable def unpackLabel : (L : LCtx τ) → (M.obj (packedExitType L) ⟶ labelObj M L)
  | [] => M.emptyIsInitial.to _
  | A :: L => (M.coprodIso A (packedExitType L)).hom ≫ coprod.desc (labelInject M 0 rfl)
      (unpackLabel L ≫ labelMap M (SSA.Ren.wk L A))

/-- The singleton label coproduct contains only its payload. -/
noncomputable def singletonLabelPayload (A : τ) : labelObj M [A] ⟶ M.obj A :=
  Sigma.desc fun i => eqToHom (by
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    rfl)

/-- Retag an exit into the singleton label carrying the packed type. -/
noncomputable def packLabelExit (L : LCtx τ) : labelObj M L ⟶ labelObj M [packedExitType L] :=
  packLabel M L ≫ labelInject M 0 rfl

/-- Drop the singleton wrapper and decode a packed payload. -/
noncomputable def unpackLabelExit (L : LCtx τ) : labelObj M [packedExitType L] ⟶ labelObj M L :=
  singletonLabelPayload M (packedExitType L) ≫ unpackLabel M L

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
