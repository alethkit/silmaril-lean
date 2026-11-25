module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial.Agreement

/-! # Finite decoded returns for partial two-exit instructions -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial

open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LetIter.ProofRelevant.Semantics

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B C D : τ} {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A C D}

set_option backward.isDefEq.respectTransparency false

/-- Finite explicit execution and the ordered RVSDG interpretation agree
on both external labels, their respective payloads, and the returned state. -/
theorem ordered_returns_iff (rel : Related A B C D r g) (env : Env [A])
    (label : LabelDen [C, D]) (initial final : σ) :
    (denote (ε := ε) (m := StateT σ Part.{u}) g env).run initial = Part.some (label, final) ↔
      returns (ε := ε) rel.instructions env.2 initial label final :=
  Proofs.ordered_returns_iff rel env label initial final

/-- For every admitted translation witness, preserve and reflect a finite
return at the actual typed LambdaSSA label and with the same final token.
Only the shared partial `StateT` instruction interpretation is required. -/
theorem region_returns_iff
    (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
      (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (rel : Related A B C D r g) (env : Env [A]) (label : LabelDen [C, D]) (initial final : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) rel.typing env).run initial = Part.some (label, final) ↔
      returns (ε := ε) rel.instructions env.2 initial label final := by
  rw [rel.chosenDenote_eq coherent]
  exact ordered_returns_iff rel env label initial final

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial
