module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Defs

/-! One θ binding with independently renumbered acyclic bodies. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta

open Continuation.Partial
open Continuation.Descent (Pending)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {args carried params results : Ports (Ty V S)}
variable {sigs sigsL sigsR : List (Ports (Ty V S))}

abbrev Body (Op : Dialect.{u, v} (ValueSort V S) S) (carried : Ports (Ty V S))
    (sigs : List (Ports (Ty V S))) := Graph Op carried [] sigs (Theta.BodyResults carried)

/-- The enclosing λ has a single θ vertex and a wiring-only suffix.
Both closures use the same typed entry and result wires. -/
abbrev code (initial : Wires args [] carried) (body : Body Op carried sigs)
    (outputs : Wires args [carried] results) :
    NestedTheta.Term (Instruction Op) args [] [carried] results :=
  .bind (Isomorphism.Invocation.loopVertex initial sigs) (fun _ => embed body.toTerm) (.ret outputs)

/-- The related carried tuples and exact shared ambient store at a restart. -/
structure Carries (m : Machine.{u, v, w} Op) (ids : GlobalRel) (σ : Type (max u v w))
    (carried : Ports (Ty V S)) where
  left : Tuple m.Val carried
  right : Tuple m.Val carried
  related : TupleRelated m ids left right
  store : σ

/-- Each side independently completes one fresh activation and selects
feedback under the actual selector convention. -/
def FeedbackPair (primitives : Primitives m σ) (left : Body Op carried sigsL) (right : Body Op carried sigsR)
    (input next : Carries m ids σ carried) : Prop :=
  Feedback.Iteration primitives (embed left.toTerm) (input.left, input.store) (next.left, next.store) ∧
  Feedback.Iteration primitives (embed right.toTerm) (input.right, input.store) (next.right, next.store)

/-- A pair of final activations after any completed feedback. A block
records the address within the sole θ body and the exact primitive site,
operands, pending frames and shared attempt store. -/
inductive FinalIteration (primitives : Primitives m σ) (rename : Renaming)
    (left : Body Op carried sigsL) (right : Body Op carried sigsR) (input : Carries m ids σ carried) :
    Continuation.Partial.Outcome m σ carried → Continuation.Partial.Outcome m σ carried → Prop where
  | exited {tag : m.Val (.control 2)} {outL outR : Tuple m.Val carried} {store : σ}
      (exits : (tag.selector.val == 1) = false) (values : TupleRelated m ids outL outR)
      (ranL : Eval primitives (.region (embed left.toTerm) input.left PUnit.unit)
        input.store (.returned (.cons tag outL) store))
      (ranR : Eval primitives (.region (embed right.toTerm) input.right PUnit.unit)
        input.store (.returned (.cons tag outR) store)) :
    FinalIteration primitives rename left right input (.returned outL store) (.returned outR store)
  | blocked {siteL siteR : Site m} {pendingL : Pending m siteL.outs (Theta.BodyResults carried)}
      {pendingR : Pending m siteR.outs (Theta.BodyResults carried)} {store : σ}
      (location : Location) (sites : SitesRelated m ids siteL siteR)
      (ranL : BlockAt primitives left.toTerm input.left PUnit.unit input.store
        location (.blocked siteL pendingL store))
      (ranR : BlockAt primitives right.toTerm input.right PUnit.unit input.store
        (rename.location location) (.blocked siteR pendingR store)) :
    FinalIteration primitives rename left right input
      (.blocked siteL (.loop (embed left.toTerm) pendingL) store)
      (.blocked siteR (.loop (embed right.toTerm) pendingR) store)

def Finishes (primitives : Primitives m σ) (rename : Renaming)
    (left : Body Op carried sigsL) (right : Body Op carried sigsR) (input : Carries m ids σ carried)
    (outcomeL outcomeR : Continuation.Partial.Outcome m σ carried) : Prop :=
  ∃ current, ReflTransGen (FeedbackPair primitives left right) input current ∧
    FinalIteration primitives rename left right current outcomeL outcomeR

/-- The selected λs have the same typed outer wiring and checked ordered
renumbering between their distinct θ bodies. Captures are related in port order. -/
inductive ScheduledLambda (m : Machine.{u, v, w} Op) (ids : GlobalRel) (rename : Renaming)
    (params results : Ports (Ty V S)) :
    m.Val (.value (.function params results)) → m.Val (.value (.function params results)) → Prop where
  | closure {context carried : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {capturesL capturesR : Tuple m.Val context}
      {left : Body Op carried sigsL} {right : Body Op carried sigsR}
      (captured : TupleRelated m ids capturesL capturesR)
      (initial : Wires (context ++ params) [] carried)
      (outputs : Wires (context ++ params) [carried] results)
      (body : OrderedGraph rename left right) :
    ScheduledLambda m ids rename params results
      (.closure capturesL (code initial left outputs).toGraph)
      (.closure capturesR (code initial right outputs).toGraph)

/-- Restart with fresh θ locals and the original λ suffix under the loop frame. -/
def restart (body : Body Op carried sigs) (outputs : Wires args [carried] results)
    (entry : Tuple m.Val args) (input : Tuple m.Val carried × σ) : Config m σ results :=
  (Feedback.Restart.mk carried sigs (embed body.toTerm) input).config (.resume (past := []) (.ret outputs) entry PUnit.unit .halt)

/-- Every observed terminal machine configuration equals this exact outcome. -/
abbrev TerminalOutcome (primitives : Primitives m σ) (source : Config m σ results)
    (outcome : Continuation.Partial.Outcome m σ results) : Prop :=
  ∀ target, TerminalPath primitives source target ↔ target = outcome.atStack .halt

/-- Observations of the actual dispatched calls. The productive branch
exhibits a common stream of related restart tuples and the actual finite
paths to its first checkpoints. -/
inductive CallPair (primitives : Primitives m σ) (ids : GlobalRel) (rename : Renaming)
    (results : Ports (Ty V S)) : Config m σ results → Config m σ results → Prop where
  | returned {sourceL sourceR : Config m σ results} {valueL valueR : Tuple m.Val results} {store : σ}
      (values : TupleRelated m ids valueL valueR)
      (left : TerminalOutcome primitives sourceL (.returned valueL store))
      (right : TerminalOutcome primitives sourceR (.returned valueR store)) :
    CallPair primitives ids rename results sourceL sourceR
  | blocked {sourceL sourceR : Config m σ results} {args carried : Ports (Ty V S)}
      {sigsL sigsR : List (Ports (Ty V S))}
      {left : Body Op carried sigsL} {right : Body Op carried sigsR}
      {initial : Carries m ids σ carried} {entryL entryR : Tuple m.Val args}
      {siteL siteR : Site m} {pendingL : Pending m siteL.outs carried} {pendingR : Pending m siteR.outs carried} {store : σ}
      (outputs : Wires args [carried] results)
      (finished : Finishes primitives rename left right initial (.blocked siteL pendingL store) (.blocked siteR pendingR store))
      (stoppedL : TerminalOutcome primitives sourceL (.blocked siteL (.bind (past := []) (.ret outputs) entryL PUnit.unit pendingL) store))
      (stoppedR : TerminalOutcome primitives sourceR (.blocked siteR (.bind (past := []) (.ret outputs) entryR PUnit.unit pendingR) store)) :
    CallPair primitives ids rename results sourceL sourceR
  | productive {sourceL sourceR : Config m σ results} {args carried : Ports (Ty V S)}
      {sigsL sigsR : List (Ports (Ty V S))}
      {left : Body Op carried sigsL} {right : Body Op carried sigsR}
      {initial : Carries m ids σ carried} {entryL entryR : Tuple m.Val args}
      (outputs : Wires args [carried] results)
      (paired : InfiniteTrace (FeedbackPair primitives left right) initial)
      (arrivedL : ReflTransGen (Step primitives) sourceL (restart left outputs entryL (initial.left, initial.store)))
      (arrivedR : ReflTransGen (Step primitives) sourceR (restart right outputs entryR (initial.right, initial.store))) :
    CallPair primitives ids rename results sourceL sourceR

/-- An ω failure precedes dispatch. Successful links expose the two actual
call configurations for the single-θ transport. -/
inductive DispatchPair (primitives : Primitives m σ) (ids : GlobalRel) (unitRename : Nat → Nat)
    (bodyRename : Renaming) (results : Ports (Ty V S)) :
    Except (Failure m σ) (Config m σ results) → Except (Failure m σ) (Config m σ results) → Prop where
  | linkBlocked {unitL unitR vertexL vertexR : Nat} {siteL siteR : Site m}
      (address : unitRename vertexL = vertexR) (identity : ids (unitL, vertexL) (unitR, vertexR))
      (sites : SitesRelated m ids siteL siteR) (store : σ) :
    DispatchPair primitives ids unitRename bodyRename results
      (.error ⟨unitL, vertexL, siteL, store⟩) (.error ⟨unitR, vertexR, siteR, store⟩)
  | invoked {sourceL sourceR : Config m σ results} (calls : CallPair primitives ids bodyRename results sourceL sourceR) :
    DispatchPair primitives ids unitRename bodyRename results (.ok sourceL) (.ok sourceR)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta
