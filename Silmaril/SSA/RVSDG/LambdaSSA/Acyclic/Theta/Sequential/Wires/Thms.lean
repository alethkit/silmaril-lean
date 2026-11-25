module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Observe

/-! # Exact observations of two explicitly threaded loops -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires

open Isotope.LambdaSSA (Region)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (iter)
open OrderedTheta (carriedData point)
open OrderedRuntime.Structured (Data Threaded RuntimeValues runtime)
open NestedTheta.ExplicitRuntime (Checked)
open TwoBlock.TwoExit (Pure enter)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B K M C J E D : τ}
variable {r : Region Φ} {g : Graph Φ A M E D}

/-- Embed any checked component into the shared dialect with the handoff
generator, preserving its execution at every open prefix. -/
theorem lift_denote {args outs : Ports (OrderedRuntime.Structured.Ty τ)} {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
    {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : NestedTheta.Term (ExplicitRuntime.Op Φ) (Threaded args) past sigs (Threaded outs)}
    (check : Checked (Pure τ) (ExplicitRuntime.Effect Φ) a b live t)
    (input : Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded args))
    (locals : Locals (RuntimeValues (TyDen (τ := τ)) σ) past) :
    (liftChecked check).1.denoteOpenWith (wireModel (ε := ε)) input locals =
      t.denoteOpenWith (ExplicitRuntime.wireModel (ε := ε)) input locals :=
  Proofs.lifted check input locals

/-- The existing structural handoff decodes an actual producer exit and
retains the exact token as it prepares the consumer's loop carrier. -/
theorem link_boundary (label : LabelDen [M,M]) (token : σ) :
    (wireModel (Φ := Φ) (ε := ε)).primitive
      (.ordered (carriedData (First A M)) (carriedData (Second M E D)) (.effect .link))
      (ExplicitRuntime.exitTuple (A := A) (label, token)) = Part.some (point (enter (merge label)) token) :=
  Proofs.link_boundary label token

/-- The second loop receives both the first return's payload and its actual
token. There is no invocation of the second action without a first return. -/
theorem graph_rounds (s : Loops Φ A B K M C J E D) (x : TyDen A) (token : σ) :
    observe (ε := ε) (graph s) x token =
      Part.map (ExplicitRuntime.exitTuple (A := M))
        (((iter (ExplicitRuntime.round (ε := ε) (m := StateT σ Part.{u}) s.first) x) >>= fun mid =>
          iter (ExplicitRuntime.round (ε := ε) (m := StateT σ Part.{u}) s.second) (merge mid)).run token) :=
  Proofs.graph_rounds s x token

theorem Related.region_observe (w : Related A B K M C J E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial =
      Part.map (ExplicitRuntime.exitTuple (A := M))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) := by
  cases w with | loops s => exact Proofs.graph_observe s coherent env initial

/-- Every finite return preserves the actual exit label, its typed
payload and the exact final token in both directions. -/
theorem Related.region_returns_iff (w : Related A B K M C J E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (label : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial label final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.some (label, final) :=
  Proofs.returns_of_observe w env label initial final (w.region_observe coherent env initial)

theorem Related.region_undefined_iff (w : Related A B K M C J E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none := by
  rw [w.region_observe coherent env initial]
  exact Proofs.map_none_iff _ _

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires
