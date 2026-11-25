module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Evaluation
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Dispatch

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local

open Continuation.Partial (Primitives Eval Config)
open PartialLink.Invocation (Request)
open Isomorphism.Invocation (request)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {rename : Renaming}
variable {args outs params results : Ports (Ty V S)} {past sigsL sigsR : List (Ports (Ty V S))}

/-- Forget only the chosen numbering maps from the structural check. -/
theorem GraphRenumbered.isomorphic {argsL argsR outsL outsR : Ports (Ty V S)}
    {left : Graph Op argsL [] sigsL outsL} {right : Graph Op argsR [] sigsR outsR}
    (checked : GraphRenumbered Op rename left right) : Graph.Isomorphic Op left right :=
  Proofs.graph_iso checked

/-- Every existing graph isomorphism admits a recorded numbering map,
before imposing any execution-order requirement. -/
theorem exists_numbering {argsL argsR outsL outsR : Ports (Ty V S)}
    {left : Graph Op argsL [] sigsL outsL} {right : Graph Op argsR [] sigsR outsR}
    (iso : Graph.Isomorphic Op left right) : ∃ rename, GraphRenumbered Op rename left right :=
  Proofs.from_graph_iso iso

/-- Erasing an address annotation recovers the existing partial evaluation,
with the same typed primitive, inputs, pending frames and attempt store. -/
theorem BlockAt.eval {term : Term Op args past sigsL outs}
    {input : Tuple m.Val args} {locals : Locals m.Val past} {store : σ} {location : Location}
    {outcome : Continuation.Partial.Outcome m σ outs}
    (blocked : BlockAt primitives term input locals store location outcome) :
    Eval primitives (.region (embed term) input locals) store outcome :=
  Proofs.block_eval blocked

/-- Aligned schedules over a typed local graph renumbering give paired
finite evaluations. Related return tuples share their final store.
A block has the mapped γ-vertex/arm path, related typed input at the
same opcode, and the exact shared attempt store. -/
theorem graph_evaluate {left : Graph Op args [] sigsL outs} {right : Graph Op args [] sigsR outs}
    (code : OrderedGraph rename left right) (respects : ActionsRespect primitives ids)
    {inputL inputR : Tuple m.Val args} (inputs : TupleRelated m ids inputL inputR) (store : σ) :
    ∃ outL outR, EvaluationPair primitives ids rename (left := left.toTerm) (right := right.toTerm)
      inputL inputR PUnit.unit PUnit.unit store outL outR :=
  Proofs.graph_evaluate code respects inputs store

/-- Typed reads agree across equal caller scopes with related locals. -/
theorem aligned_read {past : List (Ports (Ty V S))} {ports : Ports (Ty V S)}
    {inputL inputR : Tuple m.Val args} {localsL localsR : Locals m.Val past}
    (inputs : TupleRelated m ids inputL inputR) (locals : AlignedLocals m ids localsL localsR)
    (wires : Wires args past ports) :
    TupleRelated m ids (wires.read inputL localsL) (wires.read inputR localsR) :=
  Proofs.aligned_read inputs locals wires

/-- Replay an ordered suffix at the current typed caller scope and store. -/
theorem scoped_evaluate {past : List (Ports (Ty V S))}
    {left : Term Op args past sigsL outs} {right : Term Op args past sigsR outs}
    (schedule : Schedule Op .identity left right) (respects : ActionsRespect primitives ids)
    {inputL inputR : Tuple m.Val args} {localsL localsR : Locals m.Val past}
    (inputs : TupleRelated m ids inputL inputR) (locals : AlignedLocals m ids localsL localsR) (store : σ) :
    ∃ outL outR, EvaluationPair primitives ids .identity (left := left) (right := right)
      inputL inputR localsL localsR store outL outR :=
  Proofs.scoped_evaluate schedule respects inputs locals store

/-- An ordered acyclic suffix starts from the actual saved caller inputs
and the related tuple bound by the application. Its actions start at the
post-call store and retain an addressed diagnostic if they block. -/
theorem suffix_evaluate {head : Ports (Ty V S)} {left : Term Op args [head] sigsL outs} {right : Term Op args [head] sigsR outs}
    (schedule : Schedule Op .identity left right) (respects : ActionsRespect primitives ids)
    {inputL inputR : Tuple m.Val args} {valueL valueR : Tuple m.Val head}
    (inputs : TupleRelated m ids inputL inputR) (values : TupleRelated m ids valueL valueR) (store : σ) :
    ∃ outL outR, EvaluationPair primitives ids .identity (left := left) (right := right)
      inputL inputR (Locals.snoc (past := []) PUnit.unit valueL) (Locals.snoc (past := []) PUnit.unit valueR)
      store outL outR :=
  Proofs.suffix_evaluate schedule respects inputs values store

/-- A provided return or blocked endpoint is the unique reachable terminal
configuration. This reflects arbitrary observed finite machine outcomes into
the paired terminal endpoints, from either side. -/
theorem TerminalPath.target_iff {source expected target : Config m σ results}
    (observed : TerminalPath primitives source expected) :
    TerminalPath primitives source target ↔ target = expected :=
  Proofs.terminal_iff observed

/-- Successful dispatch uses the actual linked closures, original arguments,
and the exact common post-link store. The resulting pair accounts for all
finite return/block endpoints via `TerminalPath.target_iff`. -/
theorem start_linked_calls (respects : ActionsRespect primitives ids)
    {requestL requestR : Request m σ results} {exportsL : Tuple m.Val requestL.exports}
    {exportsR : Tuple m.Val requestR.exports} {store : σ}
    (linkedL : requestL.Links primitives (.linked exportsL store))
    (linkedR : requestR.Links primitives (.linked exportsR store))
    (sameParams : requestL.params = requestR.params)
    (callees : ScheduledLambda m ids rename requestR.params results
      (sameParams ▸ exportsL.get requestL.port) (exportsR.get requestR.port))
    (arguments : TupleRelated m ids (sameParams ▸ requestL.arguments) requestR.arguments) :
    ∃ sourceL sourceR, requestL.start primitives = .ok sourceL ∧ requestR.start primitives = .ok sourceR ∧
      CallPair primitives ids rename results sourceL sourceR :=
  Proofs.start_linked_calls respects linkedL linkedR sameParams callees arguments

/-- Combine ordered partial ω linking with the finite body transport.
Link diagnostics use the unit renumbering. Selected invocation diagnostics
use the distinct hierarchical renumbering of the exported λ body. -/
theorem link_then_invoke (respects : ActionsRespect primitives ids)
    {left : Omega Op args outs sigsL} {right : Omega Op args outs sigsR}
    {positions : Fin sigsL.length ≃ Fin sigsR.length} (iso : left.RenumberedBy right positions)
    (schedule : Ordered Op (renameVertex positions) args outs left.toTerm.region right.toTerm.region)
    {unitL unitR : Nat} (identities : ∀ i, ids (unitL, i) (unitR, renameVertex positions i))
    {inputL inputR : Tuple m.Val args} (imports : TupleRelated m ids inputL inputR)
    (port : Port outs (.value (.function params results)))
    {argsL argsR : Tuple m.Val params} (arguments : TupleRelated m ids argsL argsR) (store : σ)
    (admitted : ∀ {exportsL exportsR : Tuple m.Val outs} {post : σ},
      Links primitives unitL left inputL store (.linked exportsL post) →
      Links primitives unitR right inputR store (.linked exportsR post) →
      TupleRelated m ids exportsL exportsR →
      ScheduledLambda m ids rename params results (exportsL.get port) (exportsR.get port)) :
    DispatchPair primitives ids (renameVertex positions) rename results
      ((request unitL left inputL port argsL store).start primitives)
      ((request unitR right inputR port argsR store).start primitives) :=
  Proofs.link_then_invoke respects iso schedule identities imports port arguments store admitted

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local
