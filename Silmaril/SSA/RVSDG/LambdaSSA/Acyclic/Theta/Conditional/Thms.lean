module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Graph
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Source

/-! # Exact-token observation of a flat CFG and its conditional θ graph -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point)
open Silmaril.Elgot (Iterate LawfulElgotMonad)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {A L B K E D : τ}

section Kleisli

variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

/-- The actual flat region runs the entry once and enters the loop only
when the selected label is local. -/
theorem region_gate (s : Guarded Φ A L B K E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (regionTyping s) env =
      gateAction (ε := ε) s env.2 >>= fun
        | .inl external => pure external
        | .inr header => Region.denote (ε := ε) (m := m) (Theta.regionTyping s.loop) (PUnit.unit, header) :=
  Proofs.region_gate s coherent env

end Kleisli

open NestedTheta.ExplicitRuntime (boundaryResult)
open NestedTheta.ExplicitRuntime.Partial (observeErased)

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {r : Isotope.LambdaSSA.Region Φ} {g : Graph Φ A L E D}

theorem graph_observe (s : Guarded Φ A L B K E D) (x : TyDen A) (initial : σ) :
    observe (ε := ε) (graph s) x initial =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        (((gateAction (ε := ε) s x : StateT σ Part.{u} _) >>= fun
          | .inl external => pure external
          | .inr header => Silmaril.Elgot.iter
            (ExplicitRuntime.round (ε := ε) (m := StateT σ Part.{u}) s.loop) header).run initial) :=
  Proofs.graph_observe s x initial

/-- The existing numbered wire denotation observes the actual SSA label,
its typed payload and the final token, including partial primitives. -/
theorem Related.region_observe (w : Related A L B K E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) :=
  match w with
  | .guarded s => Proofs.region_observe s coherent env initial

theorem Related.region_returns_iff (w : Related A L B K E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (label : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial label final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.some (label, final) :=
  Proofs.returns_of_observe g env.2 initial final label _ (w.region_observe coherent env initial)

theorem Related.region_undefined_iff (w : Related A L B K E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none := by
  rw [w.region_observe coherent env initial]
  exact Proofs.map_none_iff _ _

/-- The same finite observation transports across single-live-token erasure. -/
theorem Related.erased_observe (w : Related A L B K E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observeErased (ExplicitRuntime.orderedModel (ε := ε) (σ := σ)) g w.checked (point env.2 initial) =
      Part.map (boundaryResult ∘ ExplicitRuntime.exitTuple (A := L))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) :=
  Proofs.erased_of_observe g w.checked env.2 initial _ (w.region_observe coherent env initial)


end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional
