module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Model.Defs

/-! # Typed exit observations of the conditional loop -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open OrderedTheta (point)
open TwoBlock.TwoExit (callCase exitLabel)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {A L B K E D : τ}

def gateAction {m : Type u → Type u} [Monad m] [InstructionModel Φ τ ε m]
    (s : Guarded Φ A L B K E D) (x : TyDen A) : m (LabelDen [E,D] ⊕ TyDen L) :=
  callCase (ε := ε) s.gate x >>= fun branch =>
    pure (branch.map (exitLabel ∘ TypeModel.coprodEquiv E D) id)

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]

noncomputable def observe (g : Graph Φ A L E D) (x : TyDen A) (initial : σ) :=
  NestedTheta.Partial.observe (ExplicitRuntime.wireModel (ε := ε)) g (point x initial)

def returns (g : Graph Φ A L E D) (x : TyDen A) (initial : σ) (label : LabelDen [E,D]) (final : σ) :=
  NestedTheta.Partial.returns (ExplicitRuntime.wireModel (ε := ε)) g (point x initial)
    (ExplicitRuntime.exitTuple (A := L) (label, final))

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional
