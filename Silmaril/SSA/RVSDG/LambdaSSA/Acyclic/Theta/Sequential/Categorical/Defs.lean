module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Defs

/-! # Sequential composition of two lowered θ computations -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (lift)
open Isotope.LambdaSSA.Semantics.Categorical (ctxObj labelObj labelInject)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Isotope.LetIter.ProofRelevant.Semantics.Categorical (splitMapCoprod)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (F : V ⥤ C) [DistributiveFreydCategory F]
  (T : TypeModel τ V) [InstructionModel F T Φ]

/-- An iteration step with local feedback in each phase and a single forward
transition. Only the second phase has an external return. -/
noncomputable def phaseStep {X Y : V} {P O : C}
    (first : F.obj X ⟶ P ⨿ F.obj X) (second : F.obj Y ⟶ O ⨿ F.obj Y)
    (handoff : P ⟶ F.obj Y) : F.obj (X ⨿ Y) ⟶ O ⨿ F.obj (X ⨿ Y) :=
  splitMapCoprod F X Y ≫ coprod.desc
    (first ≫ coprod.desc (handoff ≫ F.map (coprod.inr : Y ⟶ X ⨿ Y) ≫ coprod.inr)
      (F.map (coprod.inl : X ⟶ X ⨿ Y) ≫ coprod.inr))
    (second ≫ coprod.map (𝟙 O) (F.map (coprod.inr : Y ⟶ X ⨿ Y)))

/-- Both first-loop exits carry the same payload type and enter the second loop. -/
noncomputable def mergeLabels (M : τ) : labelObj T [M,M] ⟶ T.obj M :=
  Limits.Sigma.desc fun i => Fin.cases (motive := fun j => T.obj ([M,M].get j) ⟶ T.obj M)
    (𝟙 _) (Fin.cases (𝟙 _) (fun j => j.elim0)) i

noncomputable def handoffContext (M : τ) : labelObj T [M,M] ⟶ ctxObj T [M] :=
  lift (CartesianMonoidalCategory.toUnit _) (mergeLabels T M)

variable {A B K M N H E D : τ}

/-- The lowered loops run in order in the computation category. The handoff
is a pure map to the second loop's singleton value context. -/
noncomputable def denote [Iteration C] (s : Loops Φ A B K M N H E D) :
    F.obj (ctxObj T [A]) ⟶ F.obj (labelObj T [E,D]) :=
  Theta.Categorical.denoteLoop F T (.loop s.first) ≫ F.map (handoffContext T M) ≫
    Theta.Categorical.denoteLoop F T (.loop s.second)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical
