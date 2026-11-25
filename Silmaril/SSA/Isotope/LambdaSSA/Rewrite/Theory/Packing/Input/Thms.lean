module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputPacking

/-! # Typing and constructor-value unpacking for the packed input interface -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

/-- The input record is a constructor value. -/
theorem packedInputValue_branchValue (Γ : VCtx τ) :
    Tm.BranchValue Γ (packedInputValue Γ : Tm Φ) (packedInputType Γ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.packedInputValue_branchValue Γ

variable [HasTy Φ τ]

/-- A packed record can supply any of the original types by projection. -/
theorem packedInputProjection_hasType {Γ Δ : VCtx τ} {i : Nat} {A : τ} {a : Tm Φ}
    (hi : At Γ i A) (ha : Tm.HasType Δ a (packedInputType Γ)) :
    Tm.HasType Δ (packedInputProjection i a) A :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.packedInputProjection_hasType hi ha

theorem HasType.packInputs {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} (hr : HasType Γ r L) :
    HasType [packedInputType Γ] r.packInputs L :=
  hr.substVars (fun _ _ hi => packedInputProjection_hasType hi (.var (i := 0) rfl))

theorem HasType.unpackInputs {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : HasType [packedInputType Γ] r L) : HasType Γ (r.unpackInputs Γ) L :=
  hr.substVars (fun _ _ hi => (Proofs.SSA.Isotope.LambdaSSA.Rewrite.unpackInputs_subst hi).hasType)

/-- Unpacking preserves the opt-in CFG η equation, by constructor-value substitution. -/
theorem CfgEta.Eqv.unpackInputs {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : CfgEta.Eqv [packedInputType Γ] r s L) :
    CfgEta.Eqv Γ (r.unpackInputs Γ) (s.unpackInputs Γ) L :=
  h.substVars (fun _ _ hi => Proofs.SSA.Isotope.LambdaSSA.Rewrite.unpackInputs_subst hi)

end Silmaril.Isotope.LambdaSSA.Region
