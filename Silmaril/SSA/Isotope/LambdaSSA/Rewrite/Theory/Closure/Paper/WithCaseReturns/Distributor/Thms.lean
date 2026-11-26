module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Distributor.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseReturnDistributor

/-! # Value distributors in the case-return quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (DiscardPreservingReturn ProjectedPureReturn whiskerLeftFunctor discardArrow)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (returnRegion)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.Retained (distributorRegion)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Obj" => Paper.Extension.Singleton.ofType (Φ := Φ) Seed
set_option hygiene false in
local notation "Values" => Paper.WithCaseReturns.ValueCategory (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "W" => whiskerLeftFunctor Seed
set_option hygiene false in
local notation "Mem" => DiscardPreservingReturn Seed pe
local notation "U" => (Silmaril.unit : τ)
local infixr:70 " ×ₜ " => Silmaril.product
local infixr:65 " ⊕ₜ " => Silmaril.coprod

attribute [local instance] valueCartesian

/-- The copair of the two whiskered injections is always a value. -/
theorem forward_mem (X A B : τ) : Mem (guardedDistributorIso pe X A B).inv :=
  CaseReturnDistributor.forward_mem pe X A B

/-- At retained unit, the guarded map is a pure copair conjugated by the unit isomorphism. -/
theorem inverse_mem_at_unit (A B : τ) : Mem (guardedDistributorIso pe U A B).hom :=
  CaseReturnDistributor.inverse_mem_at_unit pe A B

/-- Lift the exact guarded comparison to values given membership of its inverse. -/
noncomputable def valueDistributorOfInverse (X A B : τ) (h : Mem (guardedDistributorIso pe X A B).hom) :
    (⟨Obj ((X ×ₜ A) ⊕ₜ (X ×ₜ B))⟩ : Values) ≅ ⟨Obj (X ×ₜ (A ⊕ₜ B))⟩ :=
  CaseReturnDistributor.valueDistributorOfInverse pe X A B h

/-- At retained unit, both maps of the exact guarded comparison are values. -/
noncomputable def valueDistributorAtUnit (A B : τ) :
    (⟨Obj ((U ×ₜ A) ⊕ₜ (U ×ₜ B))⟩ : Values) ≅ ⟨Obj (U ×ₜ (A ⊕ₜ B))⟩ :=
  CaseReturnDistributor.valueDistributorAtUnit pe A B

/-- The value isomorphism projects to the exact guarded computation isomorphism. -/
theorem map_valueDistributorOfInverse (X A B : τ) (h : Mem (guardedDistributorIso pe X A B).hom) :
    (values pe).mapIso (valueDistributorOfInverse pe X A B h) = (guardedDistributorIso pe X A B).symm :=
  CaseReturnDistributor.map_valueDistributorOfInverse pe X A B h

/-- The unit fixture computes the same guarded isomorphism in both directions. -/
theorem map_valueDistributorAtUnit (A B : τ) :
    (values (Φ := Φ) pe).mapIso (valueDistributorAtUnit pe A B) = (guardedDistributorIso pe U A B).symm :=
  CaseReturnDistributor.map_valueDistributorAtUnit pe A B

/-- The Cartesian left whisker maps to the literal computation whisker. -/
theorem valueWhisker_map (X : τ) {A B : τ}
    (f : (⟨Obj A⟩ : Values) ⟶ ⟨Obj B⟩) :
    (Paper.WithCaseReturns.values pe).map ((⟨Obj X⟩ : Values) ◁ f) =
      (W (Obj X)).map f.hom :=
  CaseReturnDistributor.value_whisker pe X f

/-- Left tensor by the exact unit preserves binary coproducts. -/
theorem valueWhiskerUnitPreservesBinary :
    PreservesColimitsOfShape (Discrete WalkingPair) (MonoidalCategory.tensorLeft (⟨Obj U⟩ : Values)) :=
  CaseReturnDistributor.valueWhiskerUnitPreservesBinary pe

/-- The exact guarded arrow lifts to a central, copying arrow of standard Paper. -/
theorem inverse_copying_lift (X A B : τ) :
    ∃ f : Paper.TypeCategory.ofType (Φ := Φ) (X ×ₜ (A ⊕ₜ B)) ⟶
        Paper.TypeCategory.ofType (Φ := Φ) ((X ×ₜ A) ⊕ₜ (X ×ₜ B)),
      Paper.TypeCategory.CentralCopies f ∧ (projection pe).map f = (guardedDistributorIso pe X A B).hom :=
  CaseReturnDistributor.inverse_copying_lift pe X A B

/-- The exact guarded arrow preserves discard. -/
theorem inverse_discard (X A B : τ) :
    (guardedDistributorIso pe X A B).hom ≫ discardArrow Seed ((X ×ₜ A) ⊕ₜ (X ×ₜ B)) =
      discardArrow Seed (X ×ₜ (A ⊕ₜ B)) :=
  CaseReturnDistributor.inverse_discard pe X A B

/-- The guarded map has a central, copying lift and preserves discard.
Its value membership is equivalent to admitting a projected pure-return representative. -/
theorem inverse_mem_iff_pure (X A B : τ) :
    Mem (guardedDistributorIso pe X A B).hom ↔ ProjectedPureReturn Seed pe (guardedDistributorIso pe X A B).hom :=
  CaseReturnDistributor.inverse_mem_iff_pure pe X A B

/-- Agreement with the typed distributor expression suffices for value membership. -/
theorem inverse_mem_of_distributor_return (X A B : τ)
    (eq : Paper.WithCaseReturns.Eqv pe [X ×ₜ (A ⊕ₜ B)] (returnRegion distributorTerm)
      (distributorRegion : Region Φ) [(X ×ₜ A) ⊕ₜ (X ×ₜ B)]) :
    Mem (guardedDistributorIso pe X A B).hom :=
  CaseReturnDistributor.inverse_mem_of_distributor_return pe X A B eq

/-- Binary distributivity for the chosen Cartesian tensor holds exactly when all
guarded inverse maps admit projected pure-return representatives. -/
theorem valueDistributive_iff :
    DistributiveTensor Values ↔ ∀ X A B : τ, ProjectedPureReturn Seed pe (guardedDistributorIso pe X A B).hom :=
  CaseReturnDistributor.valueDistributive_iff pe

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns
