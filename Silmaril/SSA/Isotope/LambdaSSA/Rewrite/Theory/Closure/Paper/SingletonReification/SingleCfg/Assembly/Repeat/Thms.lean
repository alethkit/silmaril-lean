module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedRepeat

/-! # Actual contextual steps that take the repeat arm -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.Model

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg (blockComputation carriedIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (sndMap inlMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel contextualStep retainEnvironment)
open CartesianMonoidalCategory (fst snd)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- A computation followed by the packed repeat tag runs as the update of the
retained state, followed by the right coproduct injection. -/
theorem contextualStep_repeat_of_packed {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (payload : J.obj (M.obj (product X S)) ⟶ J.obj (M.obj S))
    (tagged : denoteSingletonRegion J M hb.hasType =
      payload ≫ J.map (inlMap M S (coprod D Silmaril.empty))) :
    let E := ctxObj M [X]
    let f := J.map (carriedIso M X S).hom ≫ payload ≫ J.map (labelInject M 0 (L := [S]) rfl)
    contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) =
      retainEnvironment J (fst E (labelObj M [S])) f ≫ coprod.inr :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedRepeat.contextualStep_repeat_of_packed
    J M hb payload tagged

/-- Sending the original second coordinate to the repeat arm leaves the actual
contextual carrier unchanged. -/
theorem contextualStep_identityRepeat_of_packed {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (pureRepeat : denoteSingletonRegion J M hb.hasType =
      J.map (sndMap M X S ≫ inlMap M S (coprod D Silmaril.empty))) :
    contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) =
      coprod.inr :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedRepeat.contextualStep_identityRepeat_of_packed
    J M hb pureRepeat

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.Model
