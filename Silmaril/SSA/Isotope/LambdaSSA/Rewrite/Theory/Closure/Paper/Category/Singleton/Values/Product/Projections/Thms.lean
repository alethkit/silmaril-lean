module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Copy.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Projections.Interchange.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionCopy

/-! # Copying and interchange for the guarded projections -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches productSndBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Computing the first projection twice agrees with copying its single result. -/
theorem preservesDiagonal_productFst (A B : τ) :
    PreservesDiagonal (ofRegion (productFstBranches (Φ := Φ) A B)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionCopy.preservesDiagonal_productFst A B

/-- Computing the second projection twice agrees with copying its single result. -/
theorem preservesDiagonal_productSnd (A B : τ) :
    PreservesDiagonal (ofRegion (productSndBranches (Φ := Φ) A B)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionCopy.preservesDiagonal_productSnd A B

theorem centralCopies_productFst (A B : τ) :
    CentralCopies (ofRegion (productFstBranches (Φ := Φ) A B)) :=
  ⟨whiskerCentral_productFst A B, preservesDiagonal_productFst A B⟩

theorem centralCopies_productSnd (A B : τ) :
    CentralCopies (ofRegion (productSndBranches (Φ := Φ) A B)) :=
  ⟨whiskerCentral_productSnd A B, preservesDiagonal_productSnd A B⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
