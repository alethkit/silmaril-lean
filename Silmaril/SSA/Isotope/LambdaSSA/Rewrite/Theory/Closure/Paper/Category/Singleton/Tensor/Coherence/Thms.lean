module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Associator.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Projections.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalCoherence

/-! # Guarded coherence in the standard Paper singleton category -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open CfgEta.TypeCategory (productFstBranches productSndBranches)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local infixr:70 " ×ₜ " => product

/-- Guarded reassociation is central and preserves the diagonal. -/
theorem centralCopies_associate (A B C : τ) : CentralCopies (associate (Φ := Φ) A B C) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalCoherence.centralCopies_associate A B C

/-- The guarded braid is central and preserves the diagonal. -/
theorem centralCopies_braid (A B : τ) : CentralCopies (braid (Φ := Φ) A B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalCoherence.centralCopies_braid A B

/-- The pentagon for the guarded associator and the fixed-factor whiskerings. -/
theorem associate_pentagon (A B C D : τ) :
    whiskerRight (associate (Φ := Φ) A B C) (Obj D) ≫ associate A (B ×ₜ C) D ≫
      whiskerLeft (Obj A) (associate B C D) =
    associate (A ×ₜ B) C D ≫ associate A B (C ×ₜ D) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalCoherence.associate_pentagon A B C D

/-- Move the first factor past the other two using the guarded braid. -/
theorem braid_hexagon_forward (A B C : τ) :
    associate (Φ := Φ) A B C ≫ braid A (B ×ₜ C) ≫ associate B C A =
      whiskerRight (braid A B) (Obj C) ≫ associate B A C ≫ whiskerLeft (Obj B) (braid A C) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalCoherence.braid_hexagon_forward A B C

/-- Move the last factor past the other two using the guarded braid. -/
theorem braid_hexagon_reverse (A B C : τ) :
    unassociate (Φ := Φ) A B C ≫ braid (A ×ₜ B) C ≫ unassociate C A B =
      whiskerLeft (Obj A) (braid B C) ≫ unassociate A C B ≫ whiskerRight (braid A C) (Obj B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalCoherence.braid_hexagon_reverse A B C

/-- Dropping the intervening unit factor satisfies the triangle for the guarded projections. -/
theorem unitProjection_triangle (A B : τ) :
    associate (Φ := Φ) A Silmaril.unit B ≫ whiskerLeft (Obj A) (ofRegion (productSndBranches Silmaril.unit B)) =
      whiskerRight (ofRegion (productFstBranches A Silmaril.unit)) (Obj B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalCoherence.unitProjection_triangle A B

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
