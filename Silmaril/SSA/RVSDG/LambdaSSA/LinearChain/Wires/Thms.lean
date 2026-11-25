module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.Graph

/-! # Finite decoded returns for the checked linear-chain translation -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B C D : τ} {tail : List τ}
variable {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A C D}

set_option backward.isDefEq.respectTransparency false

/-- For either fibre, finite graph execution observes the same typed exit
and final state as the grouped body fold. -/
theorem Related.returns_iff (rel : Related A B C D tail r g) (env : Env [A])
    (label : LabelDen [C,D]) (initial final : σ) :
    (regionAction (ε := ε) (m := StateT σ Part.{u}) rel.instructions env).run initial = Part.some (label, final) ↔
      returns (ε := ε) g env.2 initial label final := by
  cases rel with
  | loop s => exact Proofs.graph_returns_iff s env label initial final

/-- Every admitted witness preserves and reflects finite execution at the
actual LambdaSSA region boundary, with the payload and token intact. -/
theorem Related.region_returns_iff (rel : Related A B C D tail r g)
    (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
      (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (label : LabelDen [C,D]) (initial final : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) rel.typing env).run initial = Part.some (label, final) ↔
      returns (ε := ε) g env.2 initial label final := by
  cases rel with
  | loop s => rw [chosenDenote_eq s coherent]; exact Proofs.graph_returns_iff s env label initial final

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain
