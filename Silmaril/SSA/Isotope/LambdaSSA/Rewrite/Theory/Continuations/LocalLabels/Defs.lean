module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms

/-! # Routing local CFG labels around an outward continuation -/

@[expose] public section

universe v₁ v₂ u₁ u₂ u₃

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (splitMapCoprod)

variable {τ : Type u₃}

/-- Keep labels in a local prefix at their original indices. -/
theorem localLabelRenaming (R L : LCtx τ) : Ren R (R ++ L) id := by
  intro i A h
  have hi := (List.getElem?_eq_some_iff.mp h).1
  simpa only [At, id_eq, List.getElem?_append_left hi] using h

/-- Move an outward label past the local prefix. -/
theorem outwardLabelRenaming (R L : LCtx τ) : Ren L (R ++ L) (R.length + ·) := by
  intro i A h
  simpa [At, List.getElem?_append_right] using h

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  [TypeFormers τ] (M : TypeModel τ V)

/-- Only outward alternatives run the continuation. Local alternatives
forward their payload and preserve their destination. -/
noncomputable def liftLocalLabels {Γ : VCtx τ} {L K : LCtx τ} (R : LCtx τ)
    (k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)) :
    J.obj (ctxObj M Γ ⊗ labelObj M (R ++ L)) ⟶ J.obj (labelObj M (R ++ K)) :=
  let E := ctxObj M Γ
  let X := labelObj M L
  let Y := labelObj M R
  J.map (E ◁ labelAppendSplit M R L) ≫
    J.map (DistributiveTensor.leftIso E X Y).inv ≫ splitMapCoprod J (E ⊗ X) (E ⊗ Y) ≫
    coprod.desc (k ≫ J.map (labelMap M (outwardLabelRenaming R K)))
      (J.map (CartesianMonoidalCategory.snd E Y ≫ labelMap M (localLabelRenaming R K)))

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
