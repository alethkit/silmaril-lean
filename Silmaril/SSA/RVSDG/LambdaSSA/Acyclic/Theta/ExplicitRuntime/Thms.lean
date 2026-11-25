module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Model.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Body
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Graph
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Kleisli

/-! # Exact preservation and reflection of partial state observations -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point)
open Silmaril.Elgot (iter)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B K E D : τ}
variable {r : Isotope.LambdaSSA.Region Φ} {g : Graph Φ A E D}

/-- The acyclic subgraph retains the data result and exact returned token. -/
theorem body_observe (b : Body Φ A B) (x : TyDen A) (token : σ) :
    (Wiring.body b).2.1.denoteOpenWith (wireModel (ε := ε) (σ := σ)) (point x token) PUnit.unit =
      Part.map (fun p => point p.1 p.2) ((bodyAction (ε := ε) (m := StateT σ Part.{u}) b x).run token) :=
  Proofs.body_denote b x token

theorem graph_observe (s : Loop Φ A B K E D) (a : TyDen A) (initial : σ) :
    observe (ε := ε) (graph s) a initial =
      Part.map (exitTuple (A := A)) ((iter (round (ε := ε) (m := StateT σ Part.{u}) s) a).run initial) :=
  Proofs.graph_observe s a initial

/-- Equality of partial observations at the actual LambdaSSA boundary. -/
theorem Related.region_observe (w : Related A B K E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial =
      Part.map (exitTuple (A := A)) ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) := by
  cases w with
  | loop s => rw [Proofs.region_round_eq s coherent env]; exact graph_observe s env.2 initial

/-- A finite graph return has exactly the decoded label, its typed payload,
and the final state observed by the actual LambdaSSA region. -/
theorem Related.region_returns_iff (w : Related A B K E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (label : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial label final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.some (label, final) :=
  Proofs.returns_of_observe g env.2 initial final label _ (w.region_observe coherent env initial)

/-- An undefined partial observation on either side is undefined on both. -/
theorem Related.region_undefined_iff (w : Related A B K E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none := by
  rw [w.region_observe coherent env initial]
  exact Proofs.map_none_iff _ _

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime
