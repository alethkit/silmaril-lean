module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.TwoBlock.Region
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.TwoBlock.Graph

/-! # Soundness of both translation fibres -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock

open Silmaril.Elgot
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LetIter.ProofRelevant.Semantics
open OrderedTheta (exit)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B : τ} {r : Region Φ} {g : Loop Φ A}

/-- Any translation witness yields a structural CFG denotation using the
ordered RVSDG result at the original typed exit boundary. -/
theorem Related.preserves (rel : Related A B r g) :
    RegionDenotes (m := m) ε rel.typing (denote (ε := ε) (m := m) g) := by
  cases rel with
  | loop s =>
    simpa only [funext (Proofs.graph_iterates (m := m) (ε := ε) s)] using Proofs.region_iterates s

/-- The chosen LambdaSSA denotation agrees with the ordered graph in coherent
Kleisli models, at the same typed exit. -/
theorem Related.chosenDenote_eq (rel : Related A B r g)
    (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)) :
    Region.denote (ε := ε) (m := m) rel.typing = denote (ε := ε) (m := m) g :=
  Proofs.chosen_eq coherent rel.preserves

/-- The CFG and numbered RVSDG loop compute the same iteration grouped at
the header boundary. Equality is of computations, including state when present. -/
theorem Related.denote_iter (rel : Related A B r g) (env : Env [A]) :
    denote (ε := ε) (m := m) g env =
      iter (round (ε := ε) (m := m) rel.instructions) env.2 >>= fun a => pure (exit a) := by
  cases rel with
  | loop s => exact Proofs.graph_iterates s env

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock
