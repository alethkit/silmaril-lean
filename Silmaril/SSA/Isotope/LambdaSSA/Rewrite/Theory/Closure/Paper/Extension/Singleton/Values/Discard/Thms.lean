module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingValues

/-! # Products with unit in the discard-preserving category -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "U" => (Silmaril.unit : τ)

set_option hygiene false in
local notation "Values" => DiscardPreservingValueCategory Seed pe

/-- The syntax unit is terminal among discard-preserving projected copying values. -/
noncomputable def discardPreservingUnitIsTerminal
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, WithUnitEta.Step Γ r s L → Seed Γ r s L) :
    IsTerminal (⟨Obj U⟩ : Values) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingValues.discardPreservingUnitIsTerminal Seed pe includeUnit

variable (includeProjection : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
  WithProjectionReturns.Step Γ r s L → Seed Γ r s L)

/-- A central copying lift of each pairing suffices for the product in the discard-preserving category. -/
noncomputable def discardPreservingFanIsLimit (A B : τ)
    (close : ∀ {X : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B},
      DiscardPreservingReturn Seed pe f → DiscardPreservingReturn Seed pe g →
      ∃ p : Paper.TypeCategory.ofType (Φ := Φ) X ⟶ Paper.TypeCategory.ofType (product A B),
        Paper.TypeCategory.CentralCopies p ∧ (projection Seed).map p = pairArrows Seed f g) :
    IsLimit (discardPreservingFan Seed pe includeProjection A B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingValues.discardPreservingFanIsLimit Seed pe includeProjection A B close

/-- The chosen fan at `A × Unit` is a product in the discard-preserving category. -/
noncomputable def discardPreservingRightUnitIsLimit (A : τ)
    (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, WithUnitEta.Step Γ r s L → Seed Γ r s L) :
    IsLimit (discardPreservingFan Seed pe includeProjection A U) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingValues.discardPreservingRightUnitIsLimit Seed pe includeProjection A includeUnit

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
