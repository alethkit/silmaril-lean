module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Transport.Thms

/-! # Normalization of the literal representative operations -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperations

open Silmaril CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Paper.Extension.Singleton (ofType ofRegion)

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations

open CfgEta.TypeCategory (whiskerLeftRegion_typed whiskerRightRegion_typed caseValueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Join" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "G" => ofType (Φ := Φ) Join

variable {A B D : τ}

theorem normalize_whiskerLeftRep (X : τ) (r : Rep (Φ := Φ) A B) :
    normalizeHom pe (Quotient.mk _ (whiskerLeftRep X r)) =
      Extension.Singleton.whiskerLeft Join (G X) (normalizeHom pe (Quotient.mk _ r)) := by
  change normalizeHom pe (rawClass pe (whiskerLeftRegion_typed X r.property.bindBranchArguments).hasType) =
    Extension.Singleton.whiskerLeft Join (G X) (ofRegion Join r.property.bindBranchArguments)
  rw [normalize_guarded]
  change _ = (Extension.Singleton.whiskerLeftFunctor Join (G X)).map
    ((Extension.Singleton.projection Join).map (Paper.TypeCategory.ofRegion r.property.bindBranchArguments))
  rw [Extension.Singleton.whiskerLeft_map, Paper.TypeCategory.whiskerLeft_ofRegion]
  rfl

theorem normalize_whiskerRightRep (X : τ) (r : Rep (Φ := Φ) A B) :
    normalizeHom pe (Quotient.mk _ (whiskerRightRep X r)) =
      Extension.Singleton.whiskerRight Join (normalizeHom pe (Quotient.mk _ r)) (G X) := by
  change normalizeHom pe (rawClass pe (whiskerRightRegion_typed X r.property.bindBranchArguments).hasType) =
    Extension.Singleton.whiskerRight Join (ofRegion Join r.property.bindBranchArguments) (G X)
  rw [normalize_guarded]
  change _ = (Extension.Singleton.whiskerRightFunctor Join (G X)).map
    ((Extension.Singleton.projection Join).map (Paper.TypeCategory.ofRegion r.property.bindBranchArguments))
  rw [Extension.Singleton.whiskerRight_map, Paper.TypeCategory.whiskerRight_ofRegion]
  rfl

theorem normalize_copairRep (r : Rep (Φ := Φ) A D) (s : Rep (Φ := Φ) B D) :
    normalizeHom pe (Quotient.mk _ (copairRep r s)) =
      Extension.Singleton.ValueCoproducts.exactCopair Join
        (normalizeHom pe (Quotient.mk _ r)) (normalizeHom pe (Quotient.mk _ s)) := by
  change ofRegion Join (copairRep r s).property.bindBranchArguments =
    Extension.Singleton.ValueCoproducts.exactCopair Join
      (ofRegion Join r.property.bindBranchArguments) (ofRegion Join s.property.bindBranchArguments)
  rw [Extension.Singleton.Generation.exactCopair_ofRegion]
  apply (Extension.Singleton.ofRegion_eq_iff Join _ _).mpr
  have h := Extension.Eqv.refl (Seed := Join)
    (caseValueBranches r.property.bindBranchArguments s.property.bindBranchArguments).hasType
  simpa only [copairRep, bindBranchArguments, renameVars_eq_substVars, bindBranchArguments_substVars] using h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperations
