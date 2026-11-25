module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Retained.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Copair

/-! # Copair and distributor obstructions in the joined quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (ProjectedPureReturn)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ValueCoproducts (CaseReturnAgreement CopairPure)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.Retained (distributorRegion_typed)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
open scoped Paper.BoundSimulation.Obstruction

universe u
variable {ε : Type u} [HasEff Empty ε] (pe : ε)

local notation "U" => (Ty.unit : Ty Empty)
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := Ty Empty) (Φ := Empty)

/-- Returning a case of two unit expressions differs from branching to their
returns, already at the exact input `Unit ⊕ Unit`. -/
theorem joined_caseReturnAgreement_fails : ¬ CaseReturnAgreement Seed pe :=
  Copair.joined_caseReturnAgreement_fails pe

/-- The copair that swaps the two unit tags has two discard-preserving value
legs, yet has no typed pure-return representative in the joined quotient. -/
theorem joined_copairPure_fails : ¬ CopairPure Seed pe :=
  Copair.joined_copairPure_fails pe

/-- The exact guarded arrow from `Unit × (Unit ⊕ Unit)` to
`(Unit × Unit) ⊕ (Unit × Unit)` has no typed pure-return representative. -/
theorem joined_guardedDistributor_not_projectedPureReturn :
    ¬ ProjectedPureReturn Seed pe (Paper.Extension.Singleton.ofRegion Seed (distributorRegion_typed U U U)) :=
  Copair.joined_guardedDistributor_not_projectedPureReturn pe

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction
