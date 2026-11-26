module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Fork.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Agreement

/-! # Exact observations of the typed loop diamond -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond

open Isotope.LambdaSSA (Region)
open Sequential
open OrderedTheta (point)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A M Y E D : τ}
variable {r : Region Φ} {g : Graph Φ A M Y E D}

/-- The common continuation consumes the selected arm's data and exact
returned token. The observation is of the real typed flat CFG. -/
theorem Related.region_observe (w : Related A M Y E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := M))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) := by
  cases w with | diamond s => exact Proofs.graph_observe s coherent env initial

/-- The decoded external label determines the payload type. The final
token is part of the same finite observation. -/
theorem Related.region_returns_iff (w : Related A M Y E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.some (exit, final) := by
  have encoded : returns (ε := ε) g env.2 initial exit final ↔
      observe (ε := ε) g env.2 initial = Part.some (ExplicitRuntime.exitTuple (A := M) (exit, final)) :=
    (NestedTheta.Partial.observe_eq_some (Wires.wireModel (ε := ε)) g (point env.2 initial) _).symm
  rw [encoded]
  rw [w.region_observe coherent env initial, Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  simp only [ExplicitRuntime.exitTuple_injective.eq_iff, exists_eq_right]

/-- Absence of a finite return is reflected at the partial observation
boundary, where blocking and infinite iteration have the same observation. -/
theorem Related.region_undefined_iff (w : Related A M Y E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none := by
  rw [w.region_observe coherent env initial]
  rw [Part.eq_none_iff', Part.eq_none_iff']
  rfl

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond
