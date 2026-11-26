module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationRepresentative

/-! # Guarded representatives of the joined chosen iterator -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (ofType ofRegion sumIso projectStep iterateChosen_projectStep)
open SyntacticCategory (iterateRegion_valueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ}

local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
local notation "Obj" => ofType (Seed)
local notation "F" => Paper.WithProjectionReturnsAndUnitEta.projection (τ := τ) (Φ := Φ)

/-- Iterating the projection of an ordinary exact-sum step gives the projection of its guarded loop. -/
theorem canonicalIterate_projection_exact
    (f : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType (Silmaril.coprod B A)) :
    canonicalIterate ((F).map f ≫ (sumIso (Seed) B A).hom) =
      (F).map (Paper.TypeCategory.iterateSum f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationRepresentative.projection_exact f

/-- Projection commutes with the chosen iterator after converting between the
ordinary and joined chosen coproducts. -/
theorem canonicalIterate_projectStep {X Y : Paper.TypeCategory (τ := τ) Φ} (f : X ⟶ Y ⨿ X) :
    canonicalIterate (projectStep (Seed) f) = (F).map (Paper.TypeCategory.iterate f) :=
  iterateChosen_projectStep (Seed) f

/-- With a region returning the exact sum, the chosen iterator is represented by
the one-block loop on that region. -/
theorem canonicalIterate_ofRegion {r : Region Φ} (hr : ValueBranches [A] r [Silmaril.coprod B A]) :
    canonicalIterate (ofRegion (Seed) hr ≫ (sumIso (Seed) B A).hom) =
      ofRegion (Seed) (iterateRegion_valueBranches hr) := by
  rw [canonicalIterate_projection_exact (Paper.TypeCategory.ofRegion hr), Paper.TypeCategory.iterateSum_ofRegion]

/-- Every arrow into the chosen coproduct has a guarded exact-sum representative.
The selected iteration is represented by the one-block loop on that same body. -/
theorem exists_canonicalIterate_body (f : Obj A ⟶ Obj B ⨿ Obj A) :
    ∃ (r : Region Φ) (hr : ValueBranches [A] r [Silmaril.coprod B A]),
      f = ofRegion (Seed) hr ≫ (sumIso (Seed) B A).hom ∧
      canonicalIterate f = ofRegion (Seed) (iterateRegion_valueBranches hr) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationRepresentative.exists_body f

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
