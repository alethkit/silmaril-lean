module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Model.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms
import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

/-! # Read the sequential categorical arrow in the partial state model -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical

open CategoryTheory
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Isotope.LambdaSSA.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (Env LabelDen LabelValue)
open Isotope.LambdaSSA.Semantics.Categorical (ofMonadicTypeModel ofMonadicInstructionModel)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B K M N H E D : τ}

/-- Interpret the categorical lowering in the induced Kleisli model, and
decode only the external label representation. State remains implicit. -/
noncomputable def stateDenote (s : Loops Φ A B K M N H E D) (env : Env [A]) :
    StateT σ Part.{u} (LabelDen [E,D]) :=
  letI := ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})
  (denote (typeJ (m := StateT σ Part.{u})) (ofMonadicTypeModel (τ := τ)) s).of
    (Agreement.envToCategorical env) >>= fun exit =>
      pure ((LabelValue.categoricalEquiv [E,D]).symm exit)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical
