module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductRepack

/-! # Structural product repacking in the Paper singleton category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory
open CfgEta.TypeCategory (productFstBranches productSndBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Pair the two syntactic projections to recover the product identity. -/
theorem pairArrows_projections (A B : τ) :
    pairArrows (ofRegion (productFstBranches (Φ := Φ) A B))
      (ofRegion (productSndBranches A B)) = 𝟙 (ofType (product A B)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductRepack.pairArrows_projections A B

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
