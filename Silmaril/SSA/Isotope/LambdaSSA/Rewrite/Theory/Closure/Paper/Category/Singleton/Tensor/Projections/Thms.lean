module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedProjections

/-! # Dropping the retained factor of a singleton computation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory
open CfgEta.TypeCategory (productFstBranches productSndBranches)
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ}

/-- Project away the fixed left factor before or after running the computation. -/
theorem whiskerLeft_productSnd (X : τ) (f : ofType (Φ := Φ) A ⟶ ofType B) :
    whiskerLeft (ofType X) f ≫ ofRegion (τ := τ) (productSndBranches X B) =
      ofRegion (τ := τ) (productSndBranches X A) ≫ f :=
  RetainedProjections.whiskerLeft_productSnd X f

/-- Project away the fixed right factor before or after running the computation. -/
theorem whiskerRight_productFst (X : τ) (f : ofType (Φ := Φ) A ⟶ ofType B) :
    whiskerRight f (ofType X) ≫ ofRegion (τ := τ) (productFstBranches B X) =
      ofRegion (τ := τ) (productFstBranches A X) ≫ f :=
  RetainedProjections.whiskerRight_productFst X f

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
