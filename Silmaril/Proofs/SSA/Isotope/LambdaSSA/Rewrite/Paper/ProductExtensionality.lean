module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Copy.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Projections.Interchange.Thms

/-! # Recovering arrows that preserve the diagonal from their projections -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductExtensionality

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory
open CfgEta.TypeCategory (productFstBranches productSndBranches)
open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "obj" => Paper.TypeCategory.ofType (Φ := Φ)

set_option backward.isDefEq.respectTransparency false in
theorem pairArrows_projections_of_preservesDiagonal {X A B : τ} (f : obj X ⟶ obj (product A B))
    (hf : PreservesDiagonal f) :
    pairArrows (f ≫ ofRegion (productFstBranches A B))
      (f ≫ ofRegion (productSndBranches A B)) = f := by
  have copy : pairArrows f f = f ≫ diagonalArrow (product A B) := hf
  calc
    _ = pairArrows f f ≫ (whiskerRight (ofRegion (productFstBranches A B)) (obj (product A B)) ≫
        whiskerLeft (obj A) (ofRegion (productSndBranches A B))) := by
      simp only [pairArrows, whiskerRight_comp, whiskerLeft_comp, Category.assoc]
      rw [← Category.assoc (whiskerRight (ofRegion (productFstBranches A B)) (obj X)),
        productFst_interchange_left A B f, Category.assoc]
    _ = f := by
      rw [copy, Category.assoc]
      change f ≫ pairArrows (ofRegion (productFstBranches A B)) (ofRegion (productSndBranches A B)) = f
      rw [pairArrows_projections, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem projection_ext_of_preservesDiagonal {X A B : τ} {f g : obj X ⟶ obj (product A B)}
    (hf : PreservesDiagonal f) (hg : PreservesDiagonal g)
    (left : f ≫ ofRegion (productFstBranches A B) = g ≫ ofRegion (productFstBranches A B))
    (right : f ≫ ofRegion (productSndBranches A B) = g ≫ ofRegion (productSndBranches A B)) :
    f = g := by
  calc
    f = pairArrows (f ≫ ofRegion (productFstBranches A B))
        (f ≫ ofRegion (productSndBranches A B)) :=
      (pairArrows_projections_of_preservesDiagonal f hf).symm
    _ = pairArrows (g ≫ ofRegion (productFstBranches A B))
        (g ≫ ofRegion (productSndBranches A B)) := congrArg₂ pairArrows left right
    _ = g := pairArrows_projections_of_preservesDiagonal g hg

theorem projection_ext_of_generated {ε : Type w} [HasEff Φ ε] {pe : ε}
    (central : PrimitiveReturnsCentral (τ := τ) (Φ := Φ) pe)
    (copy : PrimitiveReturnsCopy (τ := τ) (Φ := Φ) pe)
    {X A B : τ} {f g : obj X ⟶ obj (product A B)}
    (hf : (PureReturnGenerators (τ := τ) (Φ := Φ) pe).multiplicativeClosure f)
    (hg : (PureReturnGenerators (τ := τ) (Φ := Φ) pe).multiplicativeClosure g)
    (left : f ≫ ofRegion (productFstBranches A B) = g ≫ ofRegion (productFstBranches A B))
    (right : f ≫ ofRegion (productSndBranches A B) = g ≫ ofRegion (productSndBranches A B)) :
    f = g := by
  have h := (primitiveReturnsCopy_iff_generated pe central).mp copy
  exact projection_ext_of_preservesDiagonal (h f hf).2 (h g hg).2 left right

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductExtensionality
