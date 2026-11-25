module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs

/-! Outer θ observations using the shared ordered γ/θ activation pairing. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop

open Continuation.Partial
open Relation (ReflTransGen)
open SingleTheta (Carries)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {args carried outs : Ports (Ty V S)}
variable {sigs sigsL sigsR : List (Ports (Ty V S))}

abbrev Body (Op : Dialect.{u, v} (ValueSort V S) S) (carried : Ports (Ty V S))
    (sigs : List (Ports (Ty V S))) := Gamma.LoopBody Op carried sigs

abbrev code (initial : Wires args [] carried) (body : Body Op carried sigs)
    (outputs : Wires args [carried] outs) := Gamma.loopCode initial body outputs

abbrev IterationPair (primitives : Primitives m σ) (left : Body Op carried sigsL) (right : Body Op carried sigsR)
    (input next : Carries m ids σ carried) := Gamma.IterationPair primitives left right input next

abbrev Activation (primitives : Primitives m σ) (mapping : Renaming)
    (left : Body Op carried sigsL) (right : Body Op carried sigsR)
    (input : Carries m ids σ carried) := Gamma.Activation primitives mapping left right input

namespace Activation
export Gamma.Activation (exited blocked inner)
end Activation

abbrev LoopPair (primitives : Primitives m σ) (mapping : Renaming)
    (left : Body Op carried sigsL) (right : Body Op carried sigsR)
    (input : Carries m ids σ carried) := Gamma.LoopPair primitives mapping left right input

namespace LoopPair
export Gamma.LoopPair (activation outer)
end LoopPair

/-- Wrap the selected block in its actual saved outer loop and suffix. -/
def blockOutcome (body : Body Op carried sigs) (outputs : Wires args [carried] outs)
    (entry : Tuple m.Val args) (stop : Gamma.Block m σ (Theta.BodyResults carried)) :
    Continuation.Partial.Outcome m σ outs :=
  .blocked stop.site (.bind (past := []) (.ret outputs) entry PUnit.unit (.loop body stop.pending)) stop.store

/-- The restart configuration with the original enclosing suffix pending. -/
def restart (body : Body Op carried sigs) (outputs : Wires args [carried] outs)
    (entry : Tuple m.Val args) (input : Tuple m.Val carried × σ) : Config m σ outs :=
  (Feedback.Restart.mk carried sigs body input).config (.resume (past := []) (.ret outputs) entry PUnit.unit .halt)

/-- The first microstep of an outer activation uses fresh locals and saves
the outer loop frame in addition to the caller's suffix. -/
def active (body : Body Op carried sigs) (outputs : Wires args [carried] outs)
    (entry : Tuple m.Val args) (input : Tuple m.Val carried × σ) : Config m σ outs :=
  ⟨.eval (.region body input.1 PUnit.unit)
    (.loop body (.resume (past := []) (.ret outputs) entry PUnit.unit .halt)), input.2⟩

/-- The actual closure bodies share typed outer wiring. The outer θ is
fixed at vertex zero, and its activation uses the #2989 child witness. -/
inductive ScheduledLambda (m : Machine.{u, v, w} Op) (ids : GlobalRel) (mapping : Renaming)
    (params outs : Ports (Ty V S)) :
    m.Val (.value (.function params outs)) → m.Val (.value (.function params outs)) → Prop where
  | closure {context carried : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {capturesL capturesR : Tuple m.Val context}
      {left : Body Op carried sigsL} {right : Body Op carried sigsR}
      (captures : TupleRelated m ids capturesL capturesR)
      (initial : Wires (context ++ params) [] carried)
      (outputs : Wires (context ++ params) [carried] outs)
      (position : mapping.vertices 0 = 0)
      (ordered : Gamma.CodePair Op (mapping.child 0 0) left right) :
    ScheduledLambda m ids mapping params outs
      (.closure capturesL (code initial left outputs).toGraph)
      (.closure capturesR (code initial right outputs).toGraph)

/-- Observations from the actual call entries. Inner productivity carries
a finite outer prefix and the exact active configurations. Outer productivity
carries a common stream of completed outer activations. -/
inductive CallPair (primitives : Primitives m σ) (ids : GlobalRel) (mapping : Renaming)
    (outs : Ports (Ty V S)) : Config m σ outs → Config m σ outs → Prop where
  | returned {sourceL sourceR : Config m σ outs} {valueL valueR : Tuple m.Val outs} {store : σ}
      (values : TupleRelated m ids valueL valueR)
      (ranL : SingleTheta.TerminalOutcome primitives sourceL (.returned valueL store))
      (ranR : SingleTheta.TerminalOutcome primitives sourceR (.returned valueR store)) :
    CallPair primitives ids mapping outs sourceL sourceR
  | blocked {sourceL sourceR : Config m σ outs} {args carried : Ports (Ty V S)}
      {sigsL sigsR : List (Ports (Ty V S))} {left : Body Op carried sigsL} {right : Body Op carried sigsR}
      {entryL entryR : Tuple m.Val args} {first current : Carries m ids σ carried}
      {locL locR : Gamma.Location} {stopL stopR : Gamma.Block m σ (Theta.BodyResults carried)}
      (outputs : Wires args [carried] outs)
      (completed : ReflTransGen (IterationPair primitives left right) first current)
      (stopped : Gamma.BlockPair primitives ids (mapping.child 0 0) left right current.left current.right
        current.store locL locR stopL stopR)
      (ranL : SingleTheta.TerminalOutcome primitives sourceL (blockOutcome left outputs entryL stopL))
      (ranR : SingleTheta.TerminalOutcome primitives sourceR (blockOutcome right outputs entryR stopR)) :
    CallPair primitives ids mapping outs sourceL sourceR
  | inner {sourceL sourceR : Config m σ outs} {args carried : Ports (Ty V S)}
      {sigsL sigsR : List (Ports (Ty V S))} {left : Body Op carried sigsL} {right : Body Op carried sigsR}
      {entryL entryR : Tuple m.Val args} {first current : Carries m ids σ carried}
      (outputs : Wires args [carried] outs)
      (completed : ReflTransGen (IterationPair primitives left right) first current)
      (live : Gamma.ProductivePair primitives ids (.region left current.left PUnit.unit)
        (.region right current.right PUnit.unit) current.store)
      (enteredL : ReflTransGen (Step primitives) sourceL (active left outputs entryL (current.left, current.store)))
      (enteredR : ReflTransGen (Step primitives) sourceR (active right outputs entryR (current.right, current.store))) :
    CallPair primitives ids mapping outs sourceL sourceR
  | outer {sourceL sourceR : Config m σ outs} {args carried : Ports (Ty V S)}
      {sigsL sigsR : List (Ports (Ty V S))} {left : Body Op carried sigsL} {right : Body Op carried sigsR}
      {entryL entryR : Tuple m.Val args} {first : Carries m ids σ carried}
      (outputs : Wires args [carried] outs)
      (live : InfiniteTrace (IterationPair primitives left right) first)
      (enteredL : ReflTransGen (Step primitives) sourceL (restart left outputs entryL (first.left, first.store)))
      (enteredR : ReflTransGen (Step primitives) sourceR (restart right outputs entryR (first.right, first.store))) :
    CallPair primitives ids mapping outs sourceL sourceR

inductive DispatchPair (primitives : Primitives m σ) (ids : GlobalRel) (unitRename : Nat → Nat)
    (mapping : Renaming) (outs : Ports (Ty V S)) :
    Except (Failure m σ) (Config m σ outs) → Except (Failure m σ) (Config m σ outs) → Prop where
  | linkBlocked {unitL unitR vertexL vertexR : Nat} {siteL siteR : Site m}
      (address : unitRename vertexL = vertexR) (identity : ids (unitL, vertexL) (unitR, vertexR))
      (sites : SitesRelated m ids siteL siteR) (store : σ) :
    DispatchPair primitives ids unitRename mapping outs
      (.error ⟨unitL, vertexL, siteL, store⟩) (.error ⟨unitR, vertexR, siteR, store⟩)
  | invoked {sourceL sourceR : Config m σ outs} (calls : CallPair primitives ids mapping outs sourceL sourceR) :
    DispatchPair primitives ids unitRename mapping outs (.ok sourceL) (.ok sourceR)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop
