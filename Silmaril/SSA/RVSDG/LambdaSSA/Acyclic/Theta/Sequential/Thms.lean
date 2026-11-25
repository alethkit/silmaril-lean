module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Region

/-! # The actual flat CFG denotes two successive loop computations -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (Iterate LawfulElgotMonad)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B K M C J E D : τ}

/-- The only inter-loop edges enter the second header. The flat iteration
therefore factors through the actual denotations of the two constituent CFGs. -/
theorem region_sequential (s : Loops Φ A B K M C J E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (regionTyping s) env =
      Region.denote (ε := ε) (m := m) (Theta.regionTyping s.first) env >>= fun mid =>
        Region.denote (ε := ε) (m := m) (Theta.regionTyping s.second) (PUnit.unit, merge mid) :=
  Proofs.region_sequential s coherent env

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential
