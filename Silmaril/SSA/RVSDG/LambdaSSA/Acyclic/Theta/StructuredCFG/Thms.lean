module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Fork.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Agreement

/-! # Observation agreement for structurally generated flat CFGs -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG

open Isotope.LambdaSSA (Region)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Sequential
open Sequential.Flat.Serial (Code Agrees observe returns)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A X Z U V M Y I J L E D : τ}
variable {ps qs ts sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- A binary choice composed with a shared continuation preserves agreement
of the three components. The continuation receives the selected arm's actual
payload and token. -/
theorem branch_agrees (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : Code Φ M M M U M M ps) (q : Code Φ Y M M V M M qs) (k : Code Φ M I J L E D ts)
    {left : Flat.Fragment Φ M M M} {right : Flat.Fragment Φ Y M M} {tail : Flat.Fragment Φ M E D}
    (hp : Agrees (ε := ε) (σ := σ) left p.1.toGraph) (hq : Agrees (ε := ε) (σ := σ) right q.1.toGraph)
    (hk : Agrees (ε := ε) (σ := σ) tail k.1.toGraph)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) (Flat.link (Flat.fork left right gate) tail)
      (Wiring.branch (X := X) (Z := Z) gate p q k).1.toGraph :=
  Proofs.branch_agrees gate p q k hp hq hk coherent

theorem Syntax.agrees (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) s.source s.graph :=
  Proofs.agrees s coherent

variable {r : Isotope.LambdaSSA.Region Φ} {g : Flat.Serial.Graph Φ A X Z L E D sigs}

/-- Any witness compares the repository denotation of the actual flat CFG
with the partial observation of this numbered graph. -/
theorem Related.region_observe (w : Related A X Z L E D sigs r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) := by
  cases w with | generated s => exact s.agrees coherent env initial

theorem Related.region_returns_iff (w : Related A X Z L E D sigs r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.some (exit, final) := by
  cases w with | generated s => exact Proofs.returns_iff (s.agrees coherent) env exit initial final

theorem Related.region_undefined_iff (w : Related A X Z L E D sigs r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none := by
  rw [w.region_observe coherent env initial]
  exact Proofs.map_none_iff _ _

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG
