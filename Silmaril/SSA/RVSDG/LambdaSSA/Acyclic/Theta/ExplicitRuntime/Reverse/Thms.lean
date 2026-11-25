module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Decompose

/-! # Reverse translation and exact partial-state observations -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K E D : τ}

/-- The forward compiler supplies a decomposition for its numbered graph. -/
noncomputable def canonical (s : Loop Φ A B K E D) : Decomposition (graph s) B K :=
  Proofs.canonical s

theorem canonical_decode (s : Loop Φ A B K E D) : (canonical s).view.decode = s :=
  Proofs.canonical_decode s

theorem raise_canonical_source (s : Loop Φ A B K E D) : (raise (canonical s)).1 = region s :=
  Proofs.raise_canonical_source s

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {g : Graph Φ A E D}

theorem raise_observe (d : Decomposition g B K)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial =
      Part.map (exitTuple (A := A))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (raise d).2.typing env).run initial) :=
  (raise d).2.region_observe coherent env initial

/-- The recovered CFG has a finite return exactly at the graph's decoded
label, with the same typed payload and final token. -/
theorem raise_returns_iff (d : Decomposition g B K)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (label : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial label final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) (raise d).2.typing env).run initial =
        Part.some (label, final) :=
  (raise d).2.region_returns_iff coherent env label initial final

theorem raise_undefined_iff (d : Decomposition g B K)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) (raise d).2.typing env).run initial = Part.none :=
  (raise d).2.region_undefined_iff coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse
