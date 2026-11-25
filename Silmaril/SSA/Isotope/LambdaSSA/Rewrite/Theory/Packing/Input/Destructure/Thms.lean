module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Destructure.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputDestructure

/-! # The typed input retraction for region-level destructuring -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

theorem HasType.packInputsDestructure (hr : HasType Γ r L) :
    HasType [packedInputType Γ] (r.packInputsDestructure Γ) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputDestructure.pack_typed hr

/-- Decoding around the region preserves constructor-valued branches. -/
theorem ValueBranches.packInputsDestructure (hr : ValueBranches Γ r L) :
    ValueBranches [packedInputType Γ] (r.packInputsDestructure Γ) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputDestructure.pack_valueBranches hr

/-- The outer decoder preserves existing CFG η equations by typed renaming
and congruence under fixed binary let scrutinees. -/
theorem CfgEta.Eqv.packInputsDestructure (h : CfgEta.Eqv Γ r s L) :
    CfgEta.Eqv [packedInputType Γ] (r.packInputsDestructure Γ) (s.packInputsDestructure Γ) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputDestructure.pack_congr h

/-- Unpacking after destructuring the input record recovers the exact typed
region. Its original branch arguments and local CFG bodies are unrestricted. -/
theorem HasType.unpack_packInputsDestructure (hr : HasType Γ r L) :
    ProductBeta.Eqv Γ ((r.packInputsDestructure Γ).unpackInputs Γ) r L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputDestructure.unpack_packInputsDestructure hr

end Silmaril.Isotope.LambdaSSA.Region
