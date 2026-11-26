module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BranchNormalization.Thms

/-! # From raw joined region classes to guarded region classes -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.BranchNormalization

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "E" => Extension.Eqv (Step (τ := τ) (Φ := Φ))

/-- The two joined seeds already have guarded endpoints, so branch binding preserves their closure. -/
theorem bindBranchArguments_congr {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : E Γ r s L) : E Γ r.bindBranchArguments s.bindBranchArguments L :=
  h.bindBranchArguments_of_guardedSeed (fun h => h.elim WithProjectionReturns.Step.valueBranches
    (fun h => by cases h; exact ⟨.br rfl .unit, .br rfl (.var rfl)⟩))

def rawSetoid (Γ : VCtx τ) (L : LCtx τ) : Setoid {r : Region Φ // HasType Γ r L} where
  r r s := E Γ r.val s.val L
  iseqv := ⟨fun r => Extension.Eqv.refl r.property, Extension.Eqv.symm, Extension.Eqv.trans⟩

/-- Classes of all exactly typed regions under the joined rewrite relation. -/
abbrev RawRegionClass (Γ : VCtx τ) (L : LCtx τ) := Quotient (rawSetoid (Φ := Φ) Γ L)

/-- The guarded region classes used by finite input packing. -/
abbrev GuardedRegionClass (Γ : VCtx τ) (L : LCtx τ) :=
  Quot (fun r s : {r : Region Φ // ValueBranches Γ r L} => E Γ r.val s.val L)

variable {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

def rawClass (hr : HasType Γ r L) : RawRegionClass (Φ := Φ) Γ L := Quotient.mk _ ⟨r, hr⟩

/-- Keep the guarded representative and forget its branch-value proof. -/
def toRaw (q : GuardedRegionClass (Φ := Φ) Γ L) : RawRegionClass (Φ := Φ) Γ L :=
  Quot.liftOn q (fun r => rawClass r.property.hasType) (fun _ _ h => Quotient.sound h)

/-- Normalize an arbitrary typed class to a guarded class by binding each branch argument once. -/
def normalize (q : RawRegionClass (Φ := Φ) Γ L) : GuardedRegionClass (Φ := Φ) Γ L :=
  Quotient.liftOn q (fun r => Quot.mk _ ⟨r.val.bindBranchArguments, r.property.bindBranchArguments⟩)
    (fun _ _ h => Quot.sound (bindBranchArguments_congr h))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.BranchNormalization
