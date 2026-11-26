module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnITree

/-! # The guarded pair denotes the ordered pair of visible requests -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.ITree

open CategoryTheory
open Paper.TypeCategory.ITree.Reflection (Op Atom TreeModel Call)
open Paper.Extension.Singleton.Generation (Generated)
open Silmaril.Elgot.ITree (vis)

local notation "Join" => JoinedStep (τ := Ty Atom) (Φ := Op) false

/-- Both visible operands generate the returned pair. -/
theorem pairArrow_generated : Generated Join pairArrow :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnITree.pairArrow_generated

/-- The opt-in generator identifies the pair with its ordered binders. -/
theorem pairArrow_eq_sequenced : pairArrow = sequencedArrow :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnITree.pairArrow_eq_sequenced

/-- In the descended interpretation, poll runs before query and both receive the original input. -/
theorem pairArrow_visible (x : Operand) :
    (interpretation.map pairArrow).of x = expected x :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnITree.pairArrow_visible x

/-- The first visible event distinguishes this run from any query-first run. -/
theorem query_is_not_first (x : Operand) (k : Sum Nat Nat → TreeModel Result) :
    (interpretation.map pairArrow).of x ≠ vis (.request .query x.down) k :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnITree.query_is_not_first x k

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.ITree
