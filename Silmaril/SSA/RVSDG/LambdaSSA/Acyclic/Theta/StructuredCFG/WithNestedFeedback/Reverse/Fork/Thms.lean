module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Fork.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Fork.Complete

/-! # Completeness and agreement of graph-only mixed fork recovery -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Fork

open Sequential
open Sequential.Flat.Serial (observe returns)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq τ] [DecidableEq Φ]
variable {A X Z U M Y B K I J L E D : τ}
variable {ps ts sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {g : Flat.Serial.Graph Φ A X Z L E D sigs}

omit [DecidableEq Φ] in
theorem candidate_generated (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : StructuredCFG.Reverse.Normal Φ M M M U M M ps) (q : NestedFeedback.Loop Φ Y B K M)
    (k : StructuredCFG.Reverse.Normal Φ M I J L E D ts)
    (pl : StructuredCFG.Reverse.Supported p) (kl : StructuredCFG.Reverse.Supported k) :
    let s : Syntax Φ A X Z L E D (Selection M Y I J ++ ts) :=
      .branch gate (.structured p.toSyntax) (.nested q) (.structured k.toSyntax)
    candidate s.graph = some s :=
  Proofs.candidate_generated gate p q k pl kl

theorem reject_wiring (view : Syntax Φ A X Z L E D sigs) (parsed : candidate g = some view)
    (different : view.graph ≠ g) : recover g = none := by
  simp [recover, parsed, certify, different]

/-- With right-associated local bodies, the recovered flat CFG is the
original generated region. -/
theorem recover_generated (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : StructuredCFG.Reverse.Normal Φ M M M U M M ps) (q : NestedFeedback.Loop Φ Y B K M)
    (k : StructuredCFG.Reverse.Normal Φ M I J L E D ts)
    (pl : StructuredCFG.Reverse.Supported p) (kl : StructuredCFG.Reverse.Supported k) :
    let s : Syntax Φ A X Z L E D (Selection M Y I J ++ ts) :=
      .branch gate (.structured p.toSyntax) (.nested q) (.structured k.toSyntax)
    recover s.graph = some ⟨s.source.region, .generated s⟩ :=
  Proofs.recover_generated gate p q k pl kl

/-- All canonical emissions of this mixed fork are accepted. Ordinary
local instruction sequences may recover in right-associated form. -/
theorem recover_canonical (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : StructuredCFG.Reverse.Normal Φ M M M U M M ps) (q : NestedFeedback.Loop Φ Y B K M)
    (k : StructuredCFG.Reverse.Normal Φ M I J L E D ts) :
    let s : Syntax Φ A X Z L E D (Selection M Y I J ++ ts) :=
      .branch gate (.structured p.toSyntax) (.nested q) (.structured k.toSyntax)
    (recover s.graph).isSome = true :=
  Proofs.recover_canonical gate p q k

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Every successful recovery agrees on the full partial observation at
the boundary of the actual flat LambdaSSA region. -/
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

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Fork
