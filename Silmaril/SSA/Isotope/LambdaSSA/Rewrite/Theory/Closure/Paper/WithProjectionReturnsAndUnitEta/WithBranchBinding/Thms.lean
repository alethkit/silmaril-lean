module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedBranchBinding

/-! # Equivalence of the opt-in raw quotient and the existing guarded quotient -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region

open BranchNormalization (GuardedRegionClass)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Old" => WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
local notation "JoinedEqv" => Extension.Eqv Old

variable {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- Include the original joined relation. -/
theorem ofJoined (h : JoinedEqv Γ r s L) : Eqv Γ r s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedBranchBinding.ofJoined h

/-- A branch may evaluate its argument in a let before jumping. -/
theorem ofBranch {a : Tm Φ} {ℓ : Nat} {A : τ} (hℓ : At L ℓ A) (ha : Tm.HasType Γ a A) :
    Eqv Γ (.br ℓ a) (.let₁ a (.br ℓ (.var 0))) L :=
  .extra (.br hℓ ha) (.let₁ ha (.br hℓ (.var rfl))) (.inr (.bind hℓ ha))

/-- Normalize both endpoints into the original joined relation. -/
theorem eqv_normalize (h : Eqv Γ r s L) : JoinedEqv Γ r.bindBranchArguments s.bindBranchArguments L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedBranchBinding.eqv_normalize h

/-- Branch binding is a typed rewrite for every region in the opt-in relation. -/
theorem bindBranchArguments_eqv (hr : HasType Γ r L) : Eqv Γ r r.bindBranchArguments L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedBranchBinding.bindBranchArguments_eqv hr

/-- Opt-in equality compares exactly the normalized representatives in the old relation. -/
theorem eqv_iff_normalized (hr : HasType Γ r L) (hs : HasType Γ s L) :
    Eqv Γ r s L ↔ JoinedEqv Γ r.bindBranchArguments s.bindBranchArguments L :=
  ⟨eqv_normalize, fun h => (bindBranchArguments_eqv hr).trans
    ((ofJoined h).trans (bindBranchArguments_eqv hs).symm)⟩

/-- The branch rule identifies no additional guarded representatives. -/
theorem guarded_eqv_iff (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    Eqv Γ r s L ↔ JoinedEqv Γ r s L :=
  ⟨fun h => (Extension.Eqv.paper (.cfgEta (.native hr.bindBranchArguments_equiv))).trans
    ((eqv_normalize h).trans (.paper (.cfgEta (.native hs.bindBranchArguments_equiv.symm)))), ofJoined⟩

def normalize (q : RawRegionClass (Φ := Φ) Γ L) : GuardedRegionClass (Φ := Φ) Γ L :=
  Quotient.liftOn q (fun r => Quot.mk _ ⟨r.val.bindBranchArguments, r.property.bindBranchArguments⟩)
    (fun _ _ h => Quot.sound (eqv_normalize h))

def toRaw (q : GuardedRegionClass (Φ := Φ) Γ L) : RawRegionClass (Φ := Φ) Γ L :=
  Quot.liftOn q (fun r => rawClass r.property.hasType) (fun _ _ h => Quotient.sound (ofJoined h))

@[simp] theorem toRaw_normalize (q : RawRegionClass (Φ := Φ) Γ L) : toRaw (normalize q) = q :=
  Quotient.inductionOn q fun r => Quotient.sound (bindBranchArguments_eqv r.property).symm

@[simp] theorem normalize_toRaw (q : GuardedRegionClass (Φ := Φ) Γ L) : normalize (toRaw q) = q :=
  Quot.inductionOn q fun r =>
    Quot.sound (.paper (.cfgEta (.native r.property.bindBranchArguments_equiv.symm)))

/-- Both class maps are inverse at every finite input and exit interface. -/
def rawGuardedEquiv (Γ : VCtx τ) (L : LCtx τ) :
    RawRegionClass (Φ := Φ) Γ L ≃ GuardedRegionClass (Φ := Φ) Γ L where
  toFun := normalize
  invFun := toRaw
  left_inv := toRaw_normalize
  right_inv := normalize_toRaw

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
