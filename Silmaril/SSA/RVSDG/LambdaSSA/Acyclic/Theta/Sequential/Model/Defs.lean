module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Thms

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen LabelValue)

universe u
variable {τ : Type u} [TypeFormers τ] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]

/-- The two first-loop exits carry the same type and converge at one header. -/
def merge {M : τ} : LabelDen [M,M] → TyDen M
  | .inl x | .inr (.inl x) => x
  | .inr (.inr impossible) => nomatch impossible

/-- Inject a typed selection into the flat loop dispatcher. An external
selection already has the external label type. Otherwise enter label zero. -/
def splitEntry {L B K E D : τ} {Φ : Type u} [HasTy Φ τ] (s : Loop Φ L B K E D) :
    LabelDen [E,D] ⊕ TyDen L → LabelDen [E,D] ⊕ LabelDen (List.ofFn (Theta.localTypes s))
  | .inl external => .inl external
  | .inr input =>
    let header := LinearChain.localSite (Theta.localTypes s) [E,D] 0
    LabelValue.appendSplit _ _ (LabelValue.inject header.index header.typing input)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential
