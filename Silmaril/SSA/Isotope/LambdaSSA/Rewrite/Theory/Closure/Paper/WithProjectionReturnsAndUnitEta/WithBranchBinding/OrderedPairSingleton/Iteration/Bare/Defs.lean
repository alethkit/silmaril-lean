module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Reflection.Defs

/-! # An effectful raw iteration step with a return and a repeat reply -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Bare

open Paper.TypeCategory.ITree.Reflection (Op Atom payload Output)

/-- The branch evaluates one call whose tagged reply either returns a result or repeats. -/
def rawStep : Region Op := .br 0 (.op .poll (.var 0))

theorem rawStep_typed : HasType [payload] rawStep [Output] :=
  .br (ℓ := 0) rfl (.op (.var rfl))

/-- The exact branch-binding extension of the ordered-pair join for this profile. -/
abbrev Seed := AddBinding (Paper.WithPairReturns.JoinedStep (τ := Ty Atom) (Φ := Op) false)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Bare
