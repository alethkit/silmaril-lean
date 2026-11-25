module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms

/-! # The implicit γ/θ arrow in the ordered partial state model -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical

open CategoryTheory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ofMonadicTypeModel ofMonadicInstructionModel)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B E D : τ} {tail : List τ}

/-- The canonical strong Elgot Kleisli instance, with the same partial primitive
interpretation as the checked physical-wire theorem. -/
noncomputable def denoteState (s : Blocks Φ A B E D tail) (env : Monadic.Env [A]) :
    StateT σ Part (Monadic.CategoricalLabelDen [E,D]) :=
  letI := ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})
  (denote (typeJ (m := StateT σ Part.{u})) (ofMonadicTypeModel (τ := τ)) s).of
    (Agreement.envToCategorical env)

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical
