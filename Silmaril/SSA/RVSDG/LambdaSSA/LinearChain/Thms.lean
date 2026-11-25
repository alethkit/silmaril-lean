module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.Region

/-! # The CFG denotation of a typed linear spine -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain

open Silmaril.Elgot (Iterate LawfulElgotMonad)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B C D : τ} {tail : List τ}

/-- The actual typed CFG folds the forward body edges in order and uses
Elgot iteration only at the header's feedback boundary. -/
theorem region_denotes (s : Blocks Φ A B C D tail) :
    RegionDenotes (m := m) ε (regionTyping s) (regionAction (ε := ε) s) :=
  Proofs.region_denotes s

/-- In a coherent model the chosen region denotation is the same fold. -/
theorem chosenDenote_eq (s : Blocks Φ A B C D tail)
    (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)) :
    Region.denote (ε := ε) (m := m) (regionTyping s) = regionAction (ε := ε) s :=
  TwoBlock.regionDenote_eq_of coherent (region_denotes s)

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain
