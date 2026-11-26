module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.ITree.Thms

/-! # Comparing the weak ITree kernel at the two exit interfaces -/

public section

universe v q

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPackingITree

open CategoryTheory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithProjectionReturnsAndUnitEta (denoteArrow denoteITree)
open Paper.WithProjectionReturnsAndUnitEta.ExitPacking (packArrow denote_packArrow_eq_iff)
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

theorem kernel (compat : Compatible (κ' := κ) TypedCalls raw)
    {A : Ty κ} {L : LCtx (Ty κ)} {r s : Region Φ}
    (hr : ValueBranches [A] r L) (hs : ValueBranches [A] s L) :
    let := regionTypingCoherent raw compat
    (∀ a, denoteITree raw compat (packArrow hr) a = denoteITree raw compat (packArrow hs) a) ↔
      Silmaril.Isotope.LambdaSSA.Semantics.Categorical.denoteRegion (K) (M) hr.hasType =
        Silmaril.Isotope.LambdaSSA.Semantics.Categorical.denoteRegion (K) (M) hs.hasType := by
  let := regionTypingCoherent raw compat
  refine Iff.trans ?_ (denote_packArrow_eq_iff (K) (M) (fun _ _ => ⟨rfl, rfl⟩) hr hs)
  constructor
  · intro h
    apply Kleisli.hom_ext
    apply ConcreteCategory.coe_ext
    exact funext h
  · intro h a
    exact congrArg (fun f => f.of a) h

theorem boundKernel (compat : Compatible (κ' := κ) TypedCalls raw)
    {A : Ty κ} {L : LCtx (Ty κ)} {r s : Region Φ}
    (hr : HasType [A] r L) (hs : HasType [A] s L) :
    let := regionTypingCoherent raw compat
    (∀ a, denoteITree raw compat (packArrow hr.bindBranchArguments) a =
      denoteITree raw compat (packArrow hs.bindBranchArguments) a) ↔
      Silmaril.Isotope.LambdaSSA.Semantics.Categorical.denoteRegion (K) (M) hr =
        Silmaril.Isotope.LambdaSSA.Semantics.Categorical.denoteRegion (K) (M) hs := by
  let := regionTypingCoherent raw compat
  have central := FreydCategory.CentralUnit.unit_central (J := K)
  simpa only [← denoteRegion_bindBranchArguments (K) (M) central hr,
    ← denoteRegion_bindBranchArguments (K) (M) central hs] using
    kernel raw compat hr.bindBranchArguments hs.bindBranchArguments

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPackingITree
