module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Decompose

/-! # Observations of the recovered flat two-loop CFG -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K M C J E D : τ}

open OrderedRuntime.Structured (Data Threaded runtime)
open NestedTheta.ExplicitRuntime (Checked)
open TwoBlock.TwoExit (Pure)

/-- Embedding a local region into the link dialect preserves its label tree. -/
theorem readBody_lift {args outs : Ports (OrderedRuntime.Structured.Ty τ)} {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
    {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : NestedTheta.Term (ExplicitRuntime.Op Φ) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked (Pure τ) (ExplicitRuntime.Effect Φ) a b live t) :
    readBody (liftChecked checked).1 = some (ExplicitRuntime.Reverse.read t) :=
  Proofs.read_lift checked

/-- Every forward-generated graph supplies the reverse decomposition. -/
noncomputable def canonical (s : Loops Φ A B K M C J E D) : Decomposition (graph s) B K C J :=
  Proofs.canonical s

theorem raise_canonical (s : Loops Φ A B K M C J E D) : (raise (canonical s)).1 = region s :=
  Proofs.raise_canonical s

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {g : Graph Φ A M E D}

theorem raise_observe (d : Decomposition g B K C J)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial =
      Part.map (ExplicitRuntime.exitTuple (A := M))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (raise d).2.typing env).run initial) :=
  (raise d).2.region_observe coherent env initial

/-- The recovered region and the actual numbered graph agree on finite
returns at every decoded label, with the same payload and final token. -/
theorem raise_returns_iff (d : Decomposition g B K C J)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (label : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial label final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) (raise d).2.typing env).run initial =
        Part.some (label, final) :=
  (raise d).2.region_returns_iff coherent env label initial final

theorem raise_undefined_iff (d : Decomposition g B K C J)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) (raise d).2.typing env).run initial = Part.none :=
  (raise d).2.region_undefined_iff coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse
