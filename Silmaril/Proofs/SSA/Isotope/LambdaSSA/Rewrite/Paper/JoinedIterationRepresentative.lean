module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms

/-! # Guarded body representatives after joining -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationRepresentative

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (ofType ofRegion sumIso iterateSum iterateSum_map)
open Paper.WithProjectionReturnsAndUnitEta.Reification (canonicalIterate)
open SyntacticCategory (iterateRegion_valueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ}

local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
local notation "Obj" => ofType (Seed)
local notation "F" => Paper.WithProjectionReturnsAndUnitEta.projection (τ := τ) (Φ := Φ)

set_option backward.isDefEq.respectTransparency false in
theorem projection_exact
    (f : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType (coprod B A)) :
    canonicalIterate ((F).map f ≫ (sumIso (Seed) B A).hom) =
      (F).map (Paper.TypeCategory.iterateSum f) := by
  change iterateSum (Seed) (((F).map f ≫ (sumIso (Seed) B A).hom) ≫ (sumIso (Seed) B A).inv) = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, iterateSum_map]

set_option backward.isDefEq.respectTransparency false in
theorem exists_body (f : Obj A ⟶ Obj B ⨿ Obj A) :
    ∃ (r : Region Φ) (hr : ValueBranches [A] r [coprod B A]),
      f = ofRegion (Seed) hr ≫ (sumIso (Seed) B A).hom ∧
      canonicalIterate f = ofRegion (Seed) (iterateRegion_valueBranches hr) := by
  obtain ⟨g, hg⟩ := (F).map_surjective (X := Paper.TypeCategory.ofType A)
    (Y := Paper.TypeCategory.ofType (coprod B A)) (f ≫ (sumIso (Seed) B A).inv)
  obtain ⟨r, hr, rfl⟩ := Paper.TypeCategory.exists_ofRegion g
  have h : f = ofRegion (Seed) hr ≫ (sumIso (Seed) B A).hom := by
    change f = (F).map (Paper.TypeCategory.ofRegion hr) ≫ _
    rw [hg, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨r, hr, h, ?_⟩
  rw [h, projection_exact (Paper.TypeCategory.ofRegion hr), Paper.TypeCategory.iterateSum_ofRegion]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationRepresentative
