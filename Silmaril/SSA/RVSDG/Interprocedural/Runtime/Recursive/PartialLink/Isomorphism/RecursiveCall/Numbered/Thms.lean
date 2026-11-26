module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.ClosedFamily.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Reify

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

open Local (Renaming)
open Continuation.Partial (Primitives Step)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {args outs : Ports (Ty V S)} {past pastL pastR sigs sigsL sigsR : List (Ports (Ty V S))}
variable {mapping : Renaming} {primitives : Primitives m σ} {familyL familyR : Family m}
variable {left : Graph Op args pastL sigsL outs} {right : Graph Op args pastR sigsR outs}

/-- Split a numbered table into its actual first row and remaining rows. -/
theorem prepend_head {head : Ports (Ty V S)} (graph : Graph Op args past (head :: sigs) outs) :
    NestedTheta.Graph.prepend (past := past) (head := head) (graph.nodes 0) (graph.children 0) (suffix graph) =
      graph :=
  Proofs.prepend_head graph

/-- Reify the graph certificate through the existing table decoder. The
runtime consumes the generated schedule on the actual decoded graphs. -/
theorem Ordered.schedule (checked : Ordered Op mapping left right) :
    Schedule Op mapping.vertices left.toTerm right.toTerm :=
  Proofs.schedule checked

theorem Ordered.results_related (checked : Ordered Op mapping left right) :
    left.results.addresses.map (Address.rename mapping.vertices) = right.results.addresses :=
  Proofs.results_related checked

theorem Resolved.schedule {fn : Function V S} {left right : Closure Op m.Val fn}
    (checked : Resolved m fn left right) : ResolvedSchedule Op m fn left right := by
  cases checked with | intro graphs => exact .intro graphs.schedule

/-- Generate the paired dispatch condition while retaining the actual
resolver's selected closure, captures and fixed φ slot. -/
theorem CheckedFamily.toClosed (checked : CheckedFamily primitives ids familyL familyR) :
    ClosedFamily primitives ids familyL familyR :=
  ⟨checked.closedL, checked.closedR, fun left right paired => (checked.graphs left right paired).schedule⟩

/-- Start whole-run transport at corresponding linked exports and the
exact post-link store. The ordered partial linker supplies the export
tuple relation, so the invocation uses the actual related callable
values, including recursive slots and their capture provenance. -/
theorem CheckedFamily.runs_at_export
    (checked : CheckedFamily primitives ids familyL familyR) (actions : ActionsRespect primitives ids)
    {exports : Ports (Ty V S)} {valuesL valuesR : Tuple m.Val exports}
    (port : Port exports (.value (.function args outs))) {store : σ} {rename : Nat → Nat}
    (linked : OutcomesRelated m ids σ rename exports (.linked valuesL store) (.linked valuesR store))
    (memberL : familyL (valuesL.get port)) (memberR : familyR (valuesR.get port))
    {argumentsL argumentsR : Tuple m.Val args} (inputs : TupleRelated m ids argumentsL argumentsR)
    (admittedL : TupleIn familyL argumentsL) (admittedR : TupleIn familyR argumentsR) :
    let a := (⟨Continuation.start (.call (valuesL.get port) argumentsL), store⟩ : Continuation.Partial.Config m σ outs)
    let b := (⟨Continuation.start (.call (valuesR.get port) argumentsR), store⟩ : Continuation.Partial.Config m σ outs)
    (∃ endL endR, ReachedTerminal primitives ids a b endL endR) ∨
      (InfiniteTrace (Step primitives) a ∧ InfiniteTrace (Step primitives) b) := by
  cases linked with
  | linked values =>
    exact ClosedFamily.paired_runs actions checked.toClosed
      (Admitted.call (values.get port) inputs memberL memberR admittedL admittedR store)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered
