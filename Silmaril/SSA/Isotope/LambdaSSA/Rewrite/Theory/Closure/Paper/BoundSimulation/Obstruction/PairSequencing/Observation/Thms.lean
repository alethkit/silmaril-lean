module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ConstructorSoundness

/-! # Constructor-sequencing observations at singleton unit -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril.Isotope.LambdaSSA
open scoped Paper.BoundSimulation.Obstruction

/-- Constructor sequencing identifies closed constructor returns only if
their payload syntax agrees. The input is a single unit and is unused. -/
theorem closed_branch_injective {t u : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue [] t A) (hu : Tm.BranchValue [] u A)
    (h : Paper.WithConstructorSequencing.Eqv [.unit] (.br 0 t) (.br 0 u) [A]) : t = u :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer.closed_branch_injective ht hu h

/-- Equivalent constructor returns on a singleton unit input agree under both
typed unit observations. The raw substitutions quote the observer's payloads. -/
theorem unit_branch_observations {t u : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue [.unit] t A) (hu : Tm.BranchValue [.unit] u A)
    (h : Paper.WithConstructorSequencing.Eqv [.unit] (.br 0 t) (.br 0 u) [A]) :
    t.subst (fun _ => .unit) = u.subst (fun _ => .unit) ∧
      t.subst (fun _ => .inl .unit) = u.subst (fun _ => .inl .unit) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer.unit_branch_observations ht hu h

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing
