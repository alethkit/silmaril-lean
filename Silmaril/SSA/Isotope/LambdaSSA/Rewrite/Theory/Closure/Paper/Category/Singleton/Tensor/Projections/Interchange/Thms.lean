module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Projections.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Interchange.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ActiveProjection

/-! # Active-factor interchange of the projections -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory
open CfgEta.TypeCategory (productFstBranches productSndBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- First projection on the left factor commutes with an arbitrary computation on the right. -/
theorem productFst_interchange_left {X Y : τ} (A B : τ) (f : ofType (Φ := Φ) X ⟶ ofType Y) :
    whiskerRight (ofRegion (productFstBranches A B)) (ofType X) ≫ whiskerLeft (ofType A) f =
      whiskerLeft (ofType (product A B)) f ≫ whiskerRight (ofRegion (productFstBranches A B)) (ofType Y) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ActiveProjection.productFst_interchange_left A B f

/-- First projection satisfies both interchange squares by the guarded braid. -/
theorem whiskerCentral_productFst (A B : τ) :
    WhiskerCentral (ofRegion (productFstBranches (Φ := Φ) A B)) :=
  (whiskerCentral_iff_left _).mpr (fun {_ _} f => productFst_interchange_left A B f)

/-- Second projection on the left factor commutes with an arbitrary computation on the right. -/
theorem productSnd_interchange_left {X Y : τ} (A B : τ) (f : ofType (Φ := Φ) X ⟶ ofType Y) :
    whiskerRight (ofRegion (productSndBranches A B)) (ofType X) ≫ whiskerLeft (ofType B) f =
      whiskerLeft (ofType (product A B)) f ≫ whiskerRight (ofRegion (productSndBranches A B)) (ofType Y) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ActiveProjection.productSnd_interchange_left A B f

/-- Second projection satisfies both interchange squares by the guarded braid. -/
theorem whiskerCentral_productSnd (A B : τ) :
    WhiskerCentral (ofRegion (productSndBranches (Φ := Φ) A B)) :=
  (whiskerCentral_iff_left _).mpr (fun {_ _} f => productSnd_interchange_left A B f)


end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
