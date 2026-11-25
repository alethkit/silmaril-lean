module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Graph
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Region

/-! # Elgot soundness of both admitted two-exit fibres -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit

open Silmaril.Elgot
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LetIter.ProofRelevant.Semantics

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B C D : τ} {r : Region Φ} {g : Loop Φ A C D}

set_option backward.isDefEq.respectTransparency false

/-- Every return from the initial header has the completed carrier tag.
Only the grouped header/body transition feeds back to θ. -/
theorem Related.denoteCarrier_eq (rel : Related A B C D r g) (a : TyDen A) :
    denoteCarrier (ε := ε) (m := m) g a =
      iter (round (ε := ε) (m := m) rel.instructions) a >>= fun out => pure (finish out) := by
  cases rel with
  | loop s => exact Proofs.carrier_iterates s a

/-- The numbered graph returns at one of the two actual external labels. -/
theorem Related.denote_iter (rel : Related A B C D r g) (env : Env [A]) :
    denote (ε := ε) (m := m) g env =
      iter (round (ε := ε) (m := m) rel.instructions) env.2 >>= fun out => pure (exitLabel out) := by
  cases rel with
  | loop s => exact Proofs.graph_iterates s env

/-- Soundness for every witness in either fibre, using the real typed CFG's
structural denotation and its two-label result interface. -/
theorem Related.preserves (rel : Related A B C D r g) :
    RegionDenotes (m := m) ε rel.typing (denote (ε := ε) (m := m) g) := by
  cases rel with
  | loop s =>
    simpa only [funext (Proofs.graph_iterates (ε := ε) (m := m) s)] using Proofs.region_iterates s

/-- Coherence identifies the actual chosen LambdaSSA denotation with the
adapted RVSDG interpretation as an equality of Elgot computations. -/
theorem Related.chosenDenote_eq (rel : Related A B C D r g)
    (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)) :
    Region.denote (ε := ε) (m := m) rel.typing = denote (ε := ε) (m := m) g :=
  TwoBlock.regionDenote_eq_of coherent rel.preserves

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit
