module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.ITree.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPackingITree

/-! # Comparing the weak ITree kernel at the two exit interfaces -/

public section

universe v q

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.ExitPacking

open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

variable {κ : Type (v + 1)} [AtomValues κ] {E : Type v → Type v}
  {Φ : Type q} [HasTy Φ (Ty κ)] [HasEff Φ Bool]

attribute [local instance] typeModel categoricalInstructions

variable [InstructionModel Φ (Ty κ) Bool (ModelTree E)]
  (raw : Primitive E Φ (Sigma (AtomValues.carrier (κ := κ))))

set_option hygiene false in
local notation "TypedCalls" => ⟨fun f x =>
  InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩

local notation "K" => typeJ (m := ModelTree E)
local notation "M" => Silmaril.Isotope.LambdaSSA.Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)

/-- Equality on all typed inputs of the packed singleton ITree denotations
is exactly equality of the typed multi-exit denotations in the same model. -/
theorem denoteITree_packArrow_eq_iff (compat : Compatible (κ' := κ) TypedCalls raw)
    {A : Ty κ} {L : LCtx (Ty κ)} {r s : Region Φ}
    (hr : ValueBranches [A] r L) (hs : ValueBranches [A] s L) :
    let := regionTypingCoherent raw compat
    (∀ a, denoteITree raw compat (packArrow hr) a = denoteITree raw compat (packArrow hs) a) ↔
      Silmaril.Isotope.LambdaSSA.Semantics.Categorical.denoteRegion (K) (M) hr.hasType =
        Silmaril.Isotope.LambdaSSA.Semantics.Categorical.denoteRegion (K) (M) hs.hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPackingITree.kernel raw compat hr hs

/-- For general typed regions, bind each branch argument once before packing.
The resulting singleton kernel is the original typed region denotation kernel. -/
theorem denoteITree_packBound_eq_iff (compat : Compatible (κ' := κ) TypedCalls raw)
    {A : Ty κ} {L : LCtx (Ty κ)} {r s : Region Φ}
    (hr : HasType [A] r L) (hs : HasType [A] s L) :
    let := regionTypingCoherent raw compat
    (∀ a, denoteITree raw compat (packArrow hr.bindBranchArguments) a =
      denoteITree raw compat (packArrow hs.bindBranchArguments) a) ↔
      Silmaril.Isotope.LambdaSSA.Semantics.Categorical.denoteRegion (K) (M) hr =
        Silmaril.Isotope.LambdaSSA.Semantics.Categorical.denoteRegion (K) (M) hs :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPackingITree.boundKernel raw compat hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.ExitPacking
