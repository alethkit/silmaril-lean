module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedModel

/-! # Factorization of the actual carried step in its computation category -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.Model

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)

universe u u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ]
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification (packedPair packedDiagonal packedWhiskerRight)

section Prefix

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel τ V)

theorem packedPair_id_right {P X : τ} (f : M.obj P ⟶ M.obj X) :
    packedPair M P X P f (𝟙 (M.obj P)) = packedDiagonal M P ≫ packedWhiskerRight M P P X f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedModel.packedPair_id_right M f

end Prefix

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) {obj : τ → C} (objIso : ∀ A : τ, J.obj (M.obj A) ≅ obj A)
  {X S D : τ}


/-- The retained computation comparison is conjugation by the two packed tensor isomorphisms. -/
theorem reindexRetainLeft_tensorIso {R A B : τ} (f : J.obj (M.obj A) ⟶ J.obj (M.obj B)) :
    reindexHom J M objIso (J.map (M.productIso R A).hom ≫ retainLeft J (R := M.obj R) f ≫
      J.map (M.productIso R B).inv) =
    (packedTensorIso J M objIso R A).inv ≫ (J.obj (M.obj R) ◁ f) ≫
      (packedTensorIso J M objIso R B).hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedModel.reindexRetainLeft_tensorIso J M objIso f

/-- The reindexed value whisker is conjugation of the native computation whisker. -/
theorem reindexPackedWhiskerRight_tensorIso {R A B : τ} (f : M.obj A ⟶ M.obj B) :
    reindexHom J M objIso (J.map (packedWhiskerRight M R A B f)) =
    (packedTensorIso J M objIso A R).inv ≫ (J.map f ▷ J.obj (M.obj R)) ≫
      (packedTensorIso J M objIso B R).hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedModel.reindexPackedWhiskerRight_tensorIso J M objIso f

/-- Expose the capture, retained packed block, and routing factors of an interpreted step. -/
theorem carriedStep_factor_retained
    (b : J.obj (M.obj (product X S)) ⟶ J.obj (M.obj (packedExitType [S, D]))) :
    carriedStep J M objIso X S D b =
      capturePrefix J M objIso X S ≫
        reindexHom J M objIso (J.map (M.productIso X (product X S)).hom ≫
          retainLeft J (R := M.obj X) b ≫ J.map (M.productIso X (packedExitType [S, D])).inv) ≫
        carriedRoute J M objIso X S D :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedModel.carriedStep_factor_retained J M objIso b

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.Model
