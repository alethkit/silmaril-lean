module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Model.Defs

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open OrderedTheta (carried point)
open OrderedRuntime.Structured (RuntimeValues Threaded)
open Sequential

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A M Y E D : τ}

noncomputable def observe (g : Graph Φ A M Y E D) (input : TyDen A) (initial : σ) :
    Part (Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (carried (Result M E D)))) :=
  NestedTheta.Partial.observe (Wires.wireModel (ε := ε)) g (point input initial)

def returns (g : Graph Φ A M Y E D) (input : TyDen A) (initial : σ)
    (exit : LabelDen [E,D]) (final : σ) : Prop :=
  NestedTheta.Partial.returns (Wires.wireModel (ε := ε)) g (point input initial)
    (ExplicitRuntime.exitTuple (A := M) (exit, final))

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond
