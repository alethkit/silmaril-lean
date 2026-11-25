module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Initial.Defs
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

/-- A closed constructor input gives a tag observation at any instruction-free payload type. -/
theorem branch_observation_of_closed_input {t u w : Tm Empty} {A P : Ty Empty}
    (ht : Tm.BranchValue [P] t A) (hu : Tm.BranchValue [P] u A)
    (hw : Tm.BranchValue [] w P)
    (h : Paper.WithConstructorSequencing.Eqv [P] (.br 0 t) (.br 0 u) [A]) :
    t.subst (fun _ => w) = u.subst (fun _ => w) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer.branch_observation_of_closed_input
    ht hu hw h

/-- Equal constructor tags imply structural emptiness. The observer gives every
atomic sort a value and interprets every instruction as failing to return. -/
theorem structurallyEmpty_of_tagged_branches_eq {α : Type*} {Φ : Type*} [HasTy Φ (Ty α)] (P : Ty α)
    (h : Paper.WithConstructorSequencing.Eqv [P] (.br 0 (.inl (.var 0)) : Region Φ)
      (.br 0 (.inr (.var 0))) [.coprod P P]) : Paper.StructurallyEmpty P :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer.structurallyEmpty_of_tagged_branches_eq P h

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing
