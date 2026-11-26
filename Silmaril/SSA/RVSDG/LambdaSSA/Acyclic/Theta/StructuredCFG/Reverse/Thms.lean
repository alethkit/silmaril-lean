module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Complete

/-! # Completeness at the emitted numbering and soundness of recovered CFGs -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Sequential.Flat.Serial (observe returns)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq τ] [DecidableEq Φ]
variable {A X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {g : Sequential.Flat.Serial.Graph Φ A X Z L E D sigs}

omit [DecidableEq Φ] in
theorem candidate_generated (n : Normal Φ A X Z L E D sigs) (h : Supported n) :
    candidate n.toSyntax.graph = some n :=
  Proofs.candidate_generated n h

theorem reject_wiring (n : Normal Φ A X Z L E D sigs) (parsed : candidate g = some n)
    (different : n.toSyntax.graph ≠ g) : recognize g = none := by
  simp [recognize, parsed, certify, different]

/-- Every emitted normal layout with right-associated local bodies
recovers its original normalized syntax. -/
theorem recognize_generated (n : Normal Φ A X Z L E D sigs) (h : Supported n) :
    recognize n.toSyntax.graph = some ⟨n, rfl⟩ := by
  simp [recognize, candidate_generated n h, certify]

theorem recover_generated (n : Normal Φ A X Z L E D sigs) (h : Supported n) :
    recover n.toSyntax.graph = some ⟨n.toSyntax.source.region, .generated n.toSyntax⟩ := by
  rw [recover, recognize_generated n h]
  rfl

/-- Acceptance characterizes the numbered image of the outer normal form.
Local loop-body association may change in the recovered source. -/
theorem recover_isSome_iff (g : Sequential.Flat.Serial.Graph Φ A X Z L E D sigs) :
    (recover g).isSome = true ↔ ∃ n : Normal Φ A X Z L E D sigs, n.toSyntax.graph = g :=
  Proofs.recover_isSome_iff g

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- A successful recovery compares the actual numbered graph with the
repository denotation of the recovered flat LambdaSSA CFG. -/
theorem recover_observe {w : Fibre g} (_accepted : recover g = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial) :=
  w.2.region_observe coherent env initial

theorem recover_returns_iff {w : Fibre g} (_accepted : recover g = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial = Part.some (exit, final) :=
  w.2.region_returns_iff coherent env exit initial final

theorem recover_undefined_iff {w : Fibre g} (_accepted : recover g = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial = Part.none :=
  w.2.region_undefined_iff coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse
