module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Complete

/-! # Completeness of mixed serial recovery and its denotational agreement -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse

open Sequential
open Sequential.Flat.Serial (observe returns)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq τ] [DecidableEq Φ]
variable {A B K M I J X Z L E D : τ}
variable {qs sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {g : Flat.Serial.Graph Φ A X Z L E D sigs}

omit [DecidableEq Φ] in
theorem candidate_generated (s : NestedFeedback.Loop Φ A B K M)
    (n : StructuredCFG.Reverse.Normal Φ M I J L E D qs) (supported : StructuredCFG.Reverse.Supported n) :
    candidate (Syntax.link (.nested s) (.structured n.toSyntax)).graph =
      some (.link (.nested s) (.structured n.toSyntax)) :=
  Proofs.candidate_generated s n supported

theorem reject_wiring (view : Syntax Φ A X Z L E D sigs) (parsed : candidate g = some view)
    (different : view.graph ≠ g) : recover g = none := by
  simp [recover, parsed, certify, different]

/-- With right-associated local bodies, recovery returns the exact flat CFG. -/
theorem recover_generated (s : NestedFeedback.Loop Φ A B K M)
    (n : StructuredCFG.Reverse.Normal Φ M I J L E D qs) (supported : StructuredCFG.Reverse.Supported n) :
    let shape := Syntax.link (.nested s) (.structured n.toSyntax)
    recover shape.graph = some ⟨shape.source.region, .generated shape⟩ :=
  Proofs.recover_generated s n supported

/-- The canonical mixed pair is always accepted. The suffix's local
instruction sequences may be recovered in right-associated form. -/
theorem recover_canonical (s : NestedFeedback.Loop Φ A B K M)
    (n : StructuredCFG.Reverse.Normal Φ M I J L E D qs) :
    (recover (Syntax.link (.nested s) (.structured n.toSyntax)).graph).isSome = true :=
  Proofs.recover_canonical s n

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Agreement of the full partial observation of the graph and recovered region. -/
theorem recover_observe {w : Fibre g} (_accepted : recover g = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial) :=
  w.2.region_observe coherent env initial

/-- Every successful graph-only recovery agrees with the actual flat region
on the decoded exit, its payload and the exact final token. -/
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

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse
