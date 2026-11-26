module

public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Complete

/-! # Exact recovery and observations of the reconstructed flat CFG -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K D : τ} {g : Graph Φ A D}

section Recognition

variable [DecidableEq τ] [DecidableEq Φ]

omit [DecidableEq Φ] in
theorem candidate_generated (s : Loop Φ A B K D) :
    candidate (graph s) = some ⟨B, K, s⟩ :=
  Proofs.candidate_generated s

theorem reject_wiring (view : View Φ A D) (parsed : candidate g = some view)
    (different : graph view.2.2 ≠ g) : recognize g = none := by
  simp [recognize, parsed, certify, different]

/-- The canonical emission determines both internal types and the original
flat CFG. -/
theorem recover_generated (s : Loop Φ A B K D) :
    recover (graph s) = some ⟨B, K, region s, .generated s⟩ :=
  Proofs.recover_generated s

/-- Recovery succeeds exactly on the numbered images of the admitted
two-header shape. -/
theorem recover_isSome_iff (g : Graph Φ A D) :
    (recover g).isSome = true ↔ ∃ (B K : τ) (s : Loop Φ A B K D), graph s = g :=
  Proofs.recover_isSome_iff g

end Recognition

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Every recovered source denotes the partial observation of its input
graph in the shared model. -/
theorem fibre_observe (w : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (exitTuple (A := A))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.witness.typing env).run initial) :=
  w.witness.region_observe coherent env initial

theorem fibre_returns_iff (w : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (d : TyDen D) (initial final : σ) :
    returns (ε := ε) g env.2 initial d final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.witness.typing env).run initial = Part.some (.inl d, final) :=
  w.witness.region_returns_iff coherent env d initial final

theorem fibre_undefined_iff (w : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.witness.typing env).run initial = Part.none :=
  w.witness.region_undefined_iff coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse
