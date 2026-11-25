module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Copy.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Projections.Interchange.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductExtensionality

/-! # Projection extensionality for diagonal-preserving Paper arrows -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory
open CfgEta.TypeCategory (productFstBranches productSndBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "obj" => Paper.TypeCategory.ofType (Φ := Φ)

/-- Pairing the projections of a diagonal-preserving arrow recovers that arrow. -/
theorem pairArrows_projections_of_preservesDiagonal {X A B : τ} (f : obj X ⟶ obj (product A B))
    (hf : PreservesDiagonal f) :
    pairArrows (f ≫ ofRegion (productFstBranches A B))
      (f ≫ ofRegion (productSndBranches A B)) = f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductExtensionality.pairArrows_projections_of_preservesDiagonal f hf

/-- The syntactic projections jointly determine arrows that preserve the diagonal. -/
theorem projection_ext_of_preservesDiagonal {X A B : τ} {f g : obj X ⟶ obj (product A B)}
    (hf : PreservesDiagonal f) (hg : PreservesDiagonal g)
    (left : f ≫ ofRegion (productFstBranches A B) = g ≫ ofRegion (productFstBranches A B))
    (right : f ≫ ofRegion (productSndBranches A B) = g ≫ ofRegion (productSndBranches A B)) :
    f = g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductExtensionality.projection_ext_of_preservesDiagonal hf hg left right

/-- Projection extensionality for the constructor-and-primitive sequential fragment. -/
theorem projection_ext_of_generated {ε : Type w} [HasEff Φ ε] {pe : ε}
    (central : PrimitiveReturnsCentral (τ := τ) (Φ := Φ) pe)
    (copy : PrimitiveReturnsCopy (τ := τ) (Φ := Φ) pe)
    {X A B : τ} {f g : obj X ⟶ obj (product A B)}
    (hf : (PureReturnGenerators (τ := τ) (Φ := Φ) pe).multiplicativeClosure f)
    (hg : (PureReturnGenerators (τ := τ) (Φ := Φ) pe).multiplicativeClosure g)
    (left : f ≫ ofRegion (productFstBranches A B) = g ≫ ofRegion (productFstBranches A B))
    (right : f ≫ ofRegion (productSndBranches A B) = g ≫ ofRegion (productSndBranches A B)) :
    f = g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductExtensionality.projection_ext_of_generated central copy hf hg left right

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
