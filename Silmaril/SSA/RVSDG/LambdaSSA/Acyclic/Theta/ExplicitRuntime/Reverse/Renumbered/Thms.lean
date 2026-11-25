module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Renumbered.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Isomorphism.Thms

/-! # The decoded exit and final token at the actual graph boundary -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Renumbered

open Isotope.LambdaSSA (Region)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B K E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {g : Numbered Φ A E D sigs} {r : Region Φ}

/-- Every transported relation witness compares the actual numbered graph to
the denotation of its typed LambdaSSA source. -/
theorem Related.region_observe (w : Related g B K r)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial =
      Part.map (exitTuple (A := A))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) :=
  (NestedTheta.Partial.observe_iso w.numbering (wireModel (ε := ε)) _).trans
    (w.source.region_observe coherent env initial)

theorem Related.region_returns_iff (w : Related g B K r)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (label : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial label final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial =
        Part.some (label, final) :=
  (NestedTheta.Partial.returns_iso_iff w.numbering (wireModel (ε := ε)) _ _).trans
    (w.source.region_returns_iff coherent env label initial final)

theorem Related.region_undefined_iff (w : Related g B K r)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none := by
  rw [show observe (ε := ε) g env.2 initial = observe (ε := ε) w.representative env.2 initial
    from NestedTheta.Partial.observe_iso w.numbering (wireModel (ε := ε)) _]
  exact w.source.region_undefined_iff coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Renumbered
