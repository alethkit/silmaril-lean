module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Model.Defs

/-! # Exit and token observations of the joined numbered graph -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open OrderedTheta (point)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A I M E D : τ}

noncomputable def observe (g : Graph Φ A I M E D) (input : TyDen A) (token : σ) :=
  NestedTheta.Partial.observe (Wires.wireModel (ε := ε)) g (point input token)

def returns (g : Graph Φ A I M E D) (input : TyDen A) (initial : σ) (exit : LabelDen [E,D]) (final : σ) : Prop :=
  NestedTheta.Partial.returns (Wires.wireModel (ε := ε)) g (point input initial)
    (ExplicitRuntime.exitTuple (A := M) (exit, final))

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered
