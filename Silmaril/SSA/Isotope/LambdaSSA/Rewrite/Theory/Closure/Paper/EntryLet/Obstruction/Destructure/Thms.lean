module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Destructure.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction.FlatPaper

/-! # Entry-let does not derive re-entry after a computed product destructuring -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.EntryLetObstruction.Destructure

/-- The transfer diagnostic suppresses unary-let and case effects. A computed
product destructuring marks the original two-transfer run and leaves the
re-entered run unmarked. All contextual entry-let equations preserve it. -/
theorem reentry_ne : ¬ WithEntryLet.Eqv [] original reentered [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing.destructure_reentry_ne

end Silmaril.Isotope.LambdaSSA.Region.Paper.EntryLetObstruction.Destructure
