module

public import Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.ThreeBlock.Region
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.ThreeBlock.Graph

/-! # Soundness of the typed three-block translation -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock

open Silmaril.Elgot (Iterate LawfulElgotMonad)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {A B X C D : τ} {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A C D}

set_option backward.isDefEq.respectTransparency false

section

variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

/-- Group the three actual CFG labels at the header, leaving the exit context intact. -/
theorem Related.region_denotes (rel : Related A B X C D r g) :
    RegionDenotes (m := m) ε rel.typing (regionAction (ε := ε) rel.instructions) := by
  cases rel with
  | loop s => exact Proofs.region_iterates s

/-- In a coherent model the chosen LambdaSSA denotation is the grouped iteration. -/
theorem Related.chosenDenote_eq (rel : Related A B X C D r g)
    (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)) :
    Region.denote (ε := ε) (m := m) rel.typing = regionAction (ε := ε) rel.instructions :=
  TwoBlock.regionDenote_eq_of coherent rel.region_denotes

end

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Finite explicit execution observes the grouped iteration at its typed exit. -/
theorem Related.returns_iff (rel : Related A B X C D r g) (env : Env [A])
    (label : LabelDen [C, D]) (initial final : σ) :
    (regionAction (ε := ε) (m := StateT σ Part.{u}) rel.instructions env).run initial = Part.some (label, final) ↔
      returns (ε := ε) g env.2 initial label final := by
  cases rel with
  | loop s => exact Proofs.graph_returns_iff s env label initial final

/-- Each witness preserves and reflects a finite return of the actual
LambdaSSA region with the label's own payload type and the final token. -/
theorem Related.region_returns_iff (rel : Related A B X C D r g)
    (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
      (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (label : LabelDen [C, D]) (initial final : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) rel.typing env).run initial = Part.some (label, final) ↔
      returns (ε := ε) g env.2 initial label final := by
  rw [rel.chosenDenote_eq coherent]
  exact rel.returns_iff env label initial final

end Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock
