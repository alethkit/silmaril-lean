module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Observations.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Observations

/-! # Finite observations at both sides of a typed flat handoff -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A I B K M C J E D : τ}

/-- The conditional graph's observed exit supplies the consumer's payload
and exact initial token. The two observations are of the actual checked
component graphs. -/
theorem guarded_loop_returns_iff (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u})
      (link (Fragment.guarded p) (Fragment.loop q)).typing env).run initial = Part.some (exit, final) ↔
      ∃ (mid : LabelDen [M,M]) (token : σ),
        Conditional.returns (ε := ε) (Conditional.graph p) env.2 initial mid token ∧
        ExplicitRuntime.returns (ε := ε) (ExplicitRuntime.graph q) (merge mid) token exit final :=
  Proofs.guarded_loop_returns p q coherent env exit initial final


variable {g : Conditional.Graph Φ A I M M} {h : ExplicitRuntime.Graph Φ M E D}

/-- Recover from the pair of actual checked graphs. Each witness fixes its
local wires. The typed handoff passes the producer's exact token. -/
theorem recover_returns_iff (first : Conditional.Reverse.Decomposition g B K)
    (second : ExplicitRuntime.Reverse.Decomposition h C J)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) (recover first second).typing env).run initial =
        Part.some (exit, final) ↔
      ∃ (mid : LabelDen [M,M]) (token : σ),
        Conditional.returns (ε := ε) g env.2 initial mid token ∧
        ExplicitRuntime.returns (ε := ε) h (merge mid) token exit final :=
  Proofs.recover_returns first second coherent env exit initial final

/-- Absence of any finite return on the graph pair is the SSA partial
observation of no return. It carries no diagnosis of the cause. -/
theorem recover_undefined_iff (first : Conditional.Reverse.Decomposition g B K)
    (second : ExplicitRuntime.Reverse.Decomposition h C J)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) (recover first second).typing env).run initial = Part.none ↔
      ¬ ∃ (mid : LabelDen [M,M]) (token : σ) (exit : LabelDen [E,D]) (final : σ),
        Conditional.returns (ε := ε) g env.2 initial mid token ∧
        ExplicitRuntime.returns (ε := ε) h (merge mid) token exit final :=
  Proofs.recover_undefined first second coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat
