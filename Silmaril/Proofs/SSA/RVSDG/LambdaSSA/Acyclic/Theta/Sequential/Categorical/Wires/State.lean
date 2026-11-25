module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Wires.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Thms
import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Proofs

open CategoryTheory
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Isotope.LambdaSSA.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (Env LabelDen LabelValue)
open Isotope.LambdaSSA.Semantics.Categorical (ofMonadicTypeModel ofMonadicInstructionModel RegionTypingCoherent)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B K M N H E D : τ}

theorem stateDenote_eq (s : Loops Φ A B K M N H E D) (env : Env [A])
    (coherent : Agreement.RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    stateDenote (ε := ε) (σ := σ) s env =
      Monadic.Region.denote (ε := ε) (m := StateT σ Part.{u}) (regionTyping s) env := by
  let := ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})
  let F := typeJ (m := StateT σ Part.{u})
  let T := ofMonadicTypeModel (τ := τ)
  let : RegionTypingCoherent (Φ := Φ) F T := coherent
  have eq := Agreement.categoricalRegionDenote_eq coherent (regionTyping s) env
  rw [Agreement.categoricalRegionDenote, denoteRegion_eq F T s] at eq
  unfold stateDenote
  rw [eq]
  simp only [bind_assoc, pure_bind, Equiv.symm_apply_apply, bind_pure]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Proofs
