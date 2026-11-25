module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Defs

/-! # Payload dispatchers for typed LambdaSSA CFGs -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
  (labelObj labelInject finiteLabelObj labelObjToFinite labelAppendSplit)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (splitMapCoprod)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

variable {A X Y : τ} {L : List τ}

noncomputable def siteArrow (s : Site L X) : M.obj X ⟶ labelObj M L :=
  labelInject M s.index s.typing

noncomputable def caseArrow (p : TwoBlock.Instruction Φ A (Silmaril.coprod X Y))
    (left : Site L X) (right : Site L Y) : J.obj (M.obj A) ⟶ J.obj (labelObj M L) :=
  choice J M p ≫ coprod.desc (J.map (siteArrow M left)) (J.map (siteArrow M right))

/-- Construct a coproduct dispatch arrow from the preserved finite coproduct. -/
noncomputable def dispatch {n : Nat} (R : Fin n → τ) {T : C}
    (f : ∀ i, J.obj (M.obj (R i)) ⟶ T) : J.obj (finiteLabelObj M R) ⟶ T :=
  let objs : Fin n → V := fun i => M.obj (R i)
  letI : PreservesColimitsOfShape (Discrete (Fin n)) J := PreservesFiniteCoproducts.preserves n
  let comparison : J.obj (finiteLabelObj M R) ≅ ∐ fun i => J.obj (objs i) :=
    PreservesCoproduct.iso J objs
  comparison.hom ≫ Limits.Sigma.desc f

noncomputable def localInject {n : Nat} (R : Fin n → τ) (i : Fin n) :
    M.obj (R i) ⟶ labelObj M (List.ofFn R) :=
  labelInject M i (by simp [Isotope.SSA.At, i.isLt])

/-- Separate the external labels from the next local labels. -/
noncomputable def decodeLabels {n : Nat} (R : Fin n → τ) (L : List τ) :
    J.obj (labelObj M (List.ofFn R ++ L)) ⟶ J.obj (labelObj M L) ⨿ J.obj (labelObj M (List.ofFn R)) :=
  J.map (labelAppendSplit M (List.ofFn R) L) ≫ splitMapCoprod J _ _

/-- The step of a CFG whose blocks only use their own typed payload. -/
noncomputable def cfgStepOf {n : Nat} (R : Fin n → τ) (L : List τ)
    (arrows : ∀ i, J.obj (M.obj (R i)) ⟶ J.obj (labelObj M (List.ofFn R ++ L))) :
    J.obj (labelObj M (List.ofFn R)) ⟶ J.obj (labelObj M L) ⨿ J.obj (labelObj M (List.ofFn R)) :=
  J.map (labelObjToFinite M R) ≫ dispatch J M R arrows ≫ decodeLabels J M R L

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical
