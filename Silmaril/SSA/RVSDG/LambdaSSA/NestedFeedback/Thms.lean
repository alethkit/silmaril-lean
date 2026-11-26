module

public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Model.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.NestedFeedback.Region
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.NestedFeedback.Graph
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.NestedFeedback.Agreement

/-! # Preservation and reflection for the admitted nested feedback CFG -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {A B K D : τ}

/-- The actual flat CFG factors into nested Elgot iterations, with the
outer decision executed only after the inner loop returns. -/
theorem denote_rounds {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m]
    [LawfulElgotMonad m] [InstructionModel Φ τ ε m]
    (s : Loop Φ A B K D) (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (regionTyping s) env =
      iter (round (ε := ε) s) env.2 >>= fun d => pure (Sum.inl d) :=
  Proofs.region_round s coherent env

/-- Widening the external context leaves every extra exit unreachable. -/
theorem denote_rounds_withTail {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m]
    [LawfulElgotMonad m] [InstructionModel Φ τ ε m]
    (s : Loop Φ A B K D) (extra : List τ)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (regionTypingWithTail s extra) env =
      iter (round (ε := ε) s) env.2 >>= fun d => pure (Sum.inl d) :=
  Proofs.region_round_withTail s coherent env

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {r : Isotope.LambdaSSA.Region Φ} {g : Graph Φ A D}

/-- The graph observes the exact result and final token of the related
LambdaSSA region, using the shared partial instructions in execution order. -/
theorem Related.region_observe (w : Related A B K D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial =
      Part.map (exitTuple (A := A)) ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) :=
  Proofs.region_observe w coherent env initial

theorem Related.region_returns_iff (w : Related A B K D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (d : TyDen D) (initial final : σ) :
    returns (ε := ε) g env.2 initial d final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.some (.inl d, final) :=
  Proofs.region_returns_iff w coherent env d initial final

/-- Absence of a finite return is reflected at the LambdaSSA observation
boundary, which does not distinguish blocking from divergence. -/
theorem Related.region_undefined_iff (w : Related A B K D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none :=
  Proofs.region_undefined_iff w coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback
