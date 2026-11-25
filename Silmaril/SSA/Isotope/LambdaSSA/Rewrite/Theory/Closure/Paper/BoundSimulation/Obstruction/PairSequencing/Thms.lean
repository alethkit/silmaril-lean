module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Fixture
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ConstructorSoundness

/-! # Pair sequencing is independent of unary return fusion

The separating observer preserves every constructor of the fusion-only
contextual closure. The witness concerns pair sequencing, including
when the pair occurs inside a sum injection.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open scoped Paper.BoundSimulation.Obstruction

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors.Example (source target update constructor)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce)

/-- Unary fusion alone cannot sequence this exactly typed pair. -/
theorem pair_sequence_fails :
    ¬ Paper.Extension.Eqv (Φ := Empty) UnaryReturn.Step [source]
      (returnOnce (.pair (.let₁ (.var 0) (.var 0)) (.var 0)))
      (pairSequence (.let₁ (.var 0) (.var 0)) (.var 0)) [product source source] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.pair_sequence_fails

/-- The constructor-sequencing interface cannot be supplied by unary fusion alone. -/
theorem fusion_cannot_sequence_constructors :
    ¬ ConstructorSequencing (τ := Ty Empty) (Φ := Empty) UnaryReturn.Step :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.fusion_cannot_sequence_constructors

/-- The full mixed state return is also separated from its normalized branch. -/
theorem mixed_state_fails :
    ¬ Paper.Extension.Eqv UnaryReturn.Step [source] (returnOnce update) (.br 0 constructor) [target] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.mixed_state_fails

/-- Constructor sequencing identifies closed constructor returns only if
their payload syntax agrees. The input is a single unit and is unused. -/
theorem closed_branch_injective {t u : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue [] t A) (hu : Tm.BranchValue [] u A)
    (h : Paper.WithConstructorSequencing.Eqv [.unit] (.br 0 t) (.br 0 u) [A]) : t = u :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer.closed_branch_injective ht hu h
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (returnRegion)

/-- Discarding the result of this instruction-free pure term is inequivalent
to immediate discard even when projection returns and unit η are available. -/
theorem lowered_pure_pair_discard_fails :
    ¬ Paper.Extension.Eqv
      (fun Γ r s L => Paper.WithProjectionReturns.Step Γ r s L ∨ Paper.WithUnitEta.Step Γ r s L)
      [source]
      (compLSubst (fun _ => returnRegion (.pair (.let₁ (.var 0) (.var 0)) (.var 0) : Tm Empty))
        (fun _ => .br 0 .unit) 0)
      (.br 0 .unit) [Ty.unit] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.lowered_pure_pair_discard_fails

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing
