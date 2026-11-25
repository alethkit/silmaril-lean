module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Thms

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)

universe u
variable {τ : Type u} [TypeFormers τ] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]

/-- The two first-loop exits carry the same type and converge at one header. -/
def merge {M : τ} : LabelDen [M,M] → TyDen M
  | .inl x | .inr (.inl x) => x
  | .inr (.inr impossible) => nomatch impossible

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential
