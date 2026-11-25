module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Uniformity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # Dispatcher form of one-block pure-state simulation -/

@[expose] public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.Uniformity

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd lift)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend duplicate caseWithContext contextualLoop splitMapCoprod)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel
    routeEnvironment)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ]

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [InstructionModel J M Φ]

variable {Γ : VCtx τ} {L : LCtx τ} {A D : τ}

noncomputable def stateStep {p : Region Φ} (hp : Region.HasType (A :: Γ) p (A :: L)) :
    J.obj (ctxObj M Γ ⊗ labelObj M [A]) ⟶ J.obj (labelObj M L ⨿ labelObj M [A]) :=
  J.map (ctxObj M Γ ◁ singletonLabelPayload M A) ≫ denoteRegion J M hp ≫ J.map (labelAppendSplit M [A] L)

/-- The local simulation condition on the two chosen typed CFG bodies.
The recurrence arm applies the pure state map with the original capture. -/
def localSimulation {p q : Region Φ}
    (hp : Region.HasType (A :: Γ) p (A :: L))
    (hq : Region.HasType (D :: Γ) q (D :: L))
    (h : ctxObj M (A :: Γ) ⟶ M.obj D) : Prop :=
  let E := ctxObj M Γ
  let S := labelObj M [A]
  let T := labelObj M [D]
  let O := labelObj M L
  let h' := (E ◁ singletonLabelPayload M A) ≫ h ≫ labelInject M 0 (L := [D]) (A := D) rfl
  caseWithContext J (stateStep M J hp)
      (J.map (snd (E ⊗ S) O ≫ (coprod.inl : O ⟶ O ⨿ T)))
      (J.map ((fst E S ▷ S) ≫ h' ≫ (coprod.inr : T ⟶ O ⨿ T))) =
    J.map (lift (fst E S) h') ≫ stateStep M J hq

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.Uniformity
