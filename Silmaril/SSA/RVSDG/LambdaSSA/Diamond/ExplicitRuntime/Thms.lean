module

public import Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Model.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Graph
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Kleisli

/-! # Bidirectional finite-return correctness for the admitted diamond loop -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (iter)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B X Y K E D : τ}
variable {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A E D}

/-- The actual region's partial state denotation is the same activation loop. -/
theorem Related.region_round_eq (rel : Related A B X Y K E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) rel.typing env =
      iter (round (ε := ε) (m := StateT σ Part.{u}) rel.instructions) env.2 := by
  cases rel with | loop s => exact Proofs.region_round_eq s coherent env

/-- The graph and the ordered activation loop agree on every finite exit,
including its own typed payload and the final token. -/
theorem Related.returns_iff (rel : Related A B X Y K E D r g) (a : TyDen A)
    (label : LabelDen [E,D]) (initial final : σ) :
    (iter (round (ε := ε) (m := StateT σ Part.{u}) rel.instructions) a).run initial =
      Part.some (label, final) ↔ returns (ε := ε) g a initial label final := by
  cases rel with | loop s => exact Proofs.graph_returns_iff s a label initial final

/-- Every witness in either translation fibre preserves and reflects the
finite observations of the actual typed LambdaSSA region. -/
theorem Related.region_returns_iff (rel : Related A B X Y K E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (label : LabelDen [E,D]) (initial final : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) rel.typing env).run initial =
      Part.some (label, final) ↔ returns (ε := ε) g env.2 initial label final := by
  rw [rel.region_round_eq coherent env]
  exact rel.returns_iff env.2 label initial final

end Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime
