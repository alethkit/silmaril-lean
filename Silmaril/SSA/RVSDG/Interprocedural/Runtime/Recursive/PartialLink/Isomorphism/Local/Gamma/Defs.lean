module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Defs

/-! Selected γ composition for ordered partial execution. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma

open Continuation.Partial
open Continuation.Descent (Pending)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {args outs entry returned carried params : Ports (Ty V S)} {extra : Nat}
variable {sigsL sigsR : List (Ports (Ty V S))}

abbrev vertex (inputs : Wires args [] (.control (extra + 2) :: entry))
    (sigs : Fin (extra + 2) → List (Ports (Ty V S))) :
    NestedTheta.Node (Instruction Op) args [] returned :=
  ⟨_, .base (.gamma extra), inputs, sigs⟩

/-- A single γ followed by its typed result wiring. The suffix may read
the original region arguments as well as the selected arm's outputs. -/
abbrev code (inputs : Wires args [] (.control (extra + 2) :: entry))
    {sigs : Fin (extra + 2) → List (Ports (Ty V S))}
    (arms : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigs i) returned)
    (outputs : Wires args [returned] outs) : NestedTheta.Term (Instruction Op) args [] [returned] outs :=
  .bind (vertex inputs sigs) arms (.ret outputs)

/-- The outer γ and θ bindings are at vertex zero. The renaming's child
maps choose the arm or loop body. Acyclic leaves use their own node maps. -/
inductive Location where
  | acyclic (inner : Local.Location)
  | theta (inner : Local.Location)
  | gamma (arm : Nat) (inner : Location)
  deriving DecidableEq, Repr

def Location.rename (mapping : Renaming) : Location → Location
  | .acyclic inner => .acyclic (mapping.location inner)
  | .theta inner => .theta ((mapping.child 0 0).location inner)
  | .gamma arm inner => .gamma arm (inner.rename (mapping.child 0 arm))

/-- Recursive γ trees with ordered acyclic leaves or an ordered single-θ
leaf. Every γ and θ uses common typed input and output wiring, and only
the selected γ arm will be entered. -/
inductive CodePair (Op : Dialect.{u, v} (ValueSort V S) S) :
    {args outs : Ports (Ty V S)} → {sigsL sigsR : List (Ports (Ty V S))} →
    Renaming → NestedTheta.Term (Instruction Op) args [] sigsL outs →
    NestedTheta.Term (Instruction Op) args [] sigsR outs → Prop where
  | acyclic {args outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : Graph Op args [] sigsL outs} {right : Graph Op args [] sigsR outs}
      (ordered : OrderedGraph map left right) :
    CodePair Op map (embed left.toTerm) (embed right.toTerm)
  | theta {args carried outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : SingleTheta.Body Op carried sigsL} {right : SingleTheta.Body Op carried sigsR}
      (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
      (position : map.vertices 0 = 0) (ordered : OrderedGraph (map.child 0 0) left right) :
    CodePair Op map (SingleTheta.code initial left outputs) (SingleTheta.code initial right outputs)
  | gamma {args entry returned outs : Ports (Ty V S)} {extra : Nat} {map : Renaming}
      {sigsL sigsR : Fin (extra + 2) → List (Ports (Ty V S))}
      {armsL : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsL i) returned}
      {armsR : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsR i) returned}
      (inputs : Wires args [] (.control (extra + 2) :: entry)) (outputs : Wires args [returned] outs)
      (position : map.vertices 0 = 0) (arms : ∀ i, CodePair Op (map.child 0 i.val) (armsL i) (armsR i)) :
    CodePair Op map (code inputs armsL outputs) (code inputs armsR outputs)

/-- The existing typed primitive diagnostic and exact pending continuation. -/
structure Block (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) (outs : Ports (Ty V S)) where
  site : Site m
  pending : Pending m site.outs outs
  store : σ

def Block.outcome (stop : Block m σ outs) : Continuation.Partial.Outcome m σ outs :=
  .blocked stop.site stop.pending stop.store

/-- Body-local blocking certificates under a selected γ. The θ constructor
keeps completed feedback and the blocked fresh activation. The γ constructor
keeps the actual selector and pushes the original enclosing suffix. -/
inductive BlockPair (primitives : Primitives m σ) (ids : GlobalRel) :
    {args outs : Ports (Ty V S)} → {sigsL sigsR : List (Ports (Ty V S))} →
    (map : Renaming) →
    NestedTheta.Term (Instruction Op) args [] sigsL outs →
    NestedTheta.Term (Instruction Op) args [] sigsR outs →
    Tuple m.Val args → Tuple m.Val args → σ →
    Location → Location → Block m σ outs → Block m σ outs → Prop where
  | acyclic {args outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : Term Op args [] sigsL outs} {right : Term Op args [] sigsR outs}
      {inputL inputR : Tuple m.Val args} {start store : σ}
      {siteL siteR : Site m} {pendingL : Pending m siteL.outs outs} {pendingR : Pending m siteR.outs outs}
      (location : Local.Location) (sites : SitesRelated m ids siteL siteR)
      (ranL : Local.BlockAt primitives left inputL PUnit.unit start location (.blocked siteL pendingL store))
      (ranR : Local.BlockAt primitives right inputR PUnit.unit start (map.location location) (.blocked siteR pendingR store)) :
    BlockPair primitives ids map (embed left) (embed right) inputL inputR start
      (.acyclic location) (.acyclic (map.location location)) ⟨siteL, pendingL, store⟩ ⟨siteR, pendingR, store⟩
  | theta {args carried outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : SingleTheta.Body Op carried sigsL} {right : SingleTheta.Body Op carried sigsR}
      {entryL entryR : Tuple m.Val args} {start store : σ}
      {first current : SingleTheta.Carries m ids σ carried}
      {siteL siteR : Site m} {pendingL : Pending m siteL.outs (Theta.BodyResults carried)}
      {pendingR : Pending m siteR.outs (Theta.BodyResults carried)}
      (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
      (startsL : first.left = initial.read entryL PUnit.unit) (startsR : first.right = initial.read entryR PUnit.unit)
      (startsStore : first.store = start)
      (completed : ReflTransGen (SingleTheta.FeedbackPair primitives left right) first current)
      (location : Local.Location) (sites : SitesRelated m ids siteL siteR)
      (ranL : Local.BlockAt primitives left.toTerm current.left PUnit.unit current.store
        location (.blocked siteL pendingL store))
      (ranR : Local.BlockAt primitives right.toTerm current.right PUnit.unit current.store
        ((map.child 0 0).location location) (.blocked siteR pendingR store)) :
    BlockPair primitives ids map (SingleTheta.code initial left outputs) (SingleTheta.code initial right outputs)
      entryL entryR start (.theta location) (.theta ((map.child 0 0).location location))
      ⟨siteL, .bind (past := []) (.ret outputs) entryL PUnit.unit (.loop (embed left.toTerm) pendingL), store⟩
      ⟨siteR, .bind (past := []) (.ret outputs) entryR PUnit.unit (.loop (embed right.toTerm) pendingR), store⟩
  | gamma {args entry returned outs : Ports (Ty V S)} {extra : Nat} {map : Renaming}
      {sigsL sigsR : Fin (extra + 2) → List (Ports (Ty V S))}
      {armsL : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsL i) returned}
      {armsR : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsR i) returned}
      {entryL entryR : Tuple m.Val args} {inputL inputR : Tuple m.Val entry} {store : σ}
      {tag : Fin (extra + 2)} {locL locR : Location} {stopL stopR : Block m σ returned}
      (inputs : Wires args [] (.control (extra + 2) :: entry)) (outputs : Wires args [returned] outs)
      (selectL : inputs.read entryL PUnit.unit = .cons (.control tag) inputL)
      (selectR : inputs.read entryR PUnit.unit = .cons (.control tag) inputR)
      (selected : BlockPair primitives ids (map.child 0 tag.val) (armsL tag) (armsR tag)
        inputL inputR store locL locR stopL stopR) :
    BlockPair primitives ids map (code inputs armsL outputs) (code inputs armsR outputs) entryL entryR store
      (.gamma tag.val locL) (.gamma tag.val locR)
      ⟨stopL.site, .bind (past := []) (.ret outputs) entryL PUnit.unit stopL.pending, stopL.store⟩
      ⟨stopR.site, .bind (past := []) (.ret outputs) entryR PUnit.unit stopR.pending, stopR.store⟩

variable {ids : GlobalRel} {primitives : Primitives m σ} {mapping : Renaming}

/-- A common productive feedback stream and finite syntax-directed routes
to its first checkpoints. Both routes retain all pending typed frames. -/
inductive ProductivePair (primitives : Primitives m σ) (ids : GlobalRel)
    {outs : Ports (Ty V S)} (jobL jobR : Job m outs) (store : σ) : Prop where
  | reached {carried : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {left : SingleTheta.Body Op carried sigsL} {right : SingleTheta.Body Op carried sigsR}
      {initial : SingleTheta.Carries m ids σ carried}
      {pendingL pendingR : Pending m carried outs}
      (paired : InfiniteTrace (SingleTheta.FeedbackPair primitives left right) initial)
      (ranL : Feedback.Reaches primitives jobL store ⟨carried, sigsL, embed left.toTerm, (initial.left, initial.store)⟩ pendingL)
      (ranR : Feedback.Reaches primitives jobR store ⟨carried, sigsR, embed right.toTerm, (initial.right, initial.store)⟩ pendingR)

inductive RegionPair (primitives : Primitives m σ) (ids : GlobalRel) (mapping : Renaming)
    (left : NestedTheta.Term (Instruction Op) args [] sigsL outs)
    (right : NestedTheta.Term (Instruction Op) args [] sigsR outs)
    (inputL inputR : Tuple m.Val args) (store : σ) : Prop where
  | returned {leftValue rightValue : Tuple m.Val outs} {finalStore : σ}
      (values : TupleRelated m ids leftValue rightValue)
      (ranL : Eval primitives (.region left inputL PUnit.unit) store (.returned leftValue finalStore))
      (ranR : Eval primitives (.region right inputR PUnit.unit) store (.returned rightValue finalStore))
  | blocked {locL locR : Location} {stopL stopR : Block m σ outs}
      (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR)
  | productive (run : ProductivePair primitives ids (.region left inputL PUnit.unit) (.region right inputR PUnit.unit) store)

inductive ScheduledLambda (m : Machine.{u, v, w} Op) (ids : GlobalRel) (mapping : Renaming)
    (params outs : Ports (Ty V S)) :
    m.Val (.value (.function params outs)) → m.Val (.value (.function params outs)) → Prop where
  | closure {captured : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {captL captR : Tuple m.Val captured}
      {left : NestedTheta.Term (Instruction Op) (captured ++ params) [] sigsL outs}
      {right : NestedTheta.Term (Instruction Op) (captured ++ params) [] sigsR outs}
      (captures : TupleRelated m ids captL captR) (code : CodePair Op mapping left right) :
    ScheduledLambda m ids mapping params outs (.closure captL left.toGraph) (.closure captR right.toGraph)

/-- Finite observations and productive feedback at the two call entries.
The original entries are the actual selected closures and post-link store. -/
inductive CallPair (primitives : Primitives m σ) (ids : GlobalRel) (mapping : Renaming)
    (outs : Ports (Ty V S)) : Config m σ outs → Config m σ outs → Prop where
  | returned {sourceL sourceR : Config m σ outs} {valueL valueR : Tuple m.Val outs} {store : σ}
      (values : TupleRelated m ids valueL valueR)
      (ranL : SingleTheta.TerminalOutcome primitives sourceL (.returned valueL store))
      (ranR : SingleTheta.TerminalOutcome primitives sourceR (.returned valueR store)) :
    CallPair primitives ids mapping outs sourceL sourceR
  | blocked {sourceL sourceR : Config m σ outs}
      {args : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {left : NestedTheta.Term (Instruction Op) args [] sigsL outs}
      {right : NestedTheta.Term (Instruction Op) args [] sigsR outs}
      {inputL inputR : Tuple m.Val args} {store : σ} {locL locR : Location} {stopL stopR : Block m σ outs}
      (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR)
      (ranL : SingleTheta.TerminalOutcome primitives sourceL stopL.outcome)
      (ranR : SingleTheta.TerminalOutcome primitives sourceR stopR.outcome) :
    CallPair primitives ids mapping outs sourceL sourceR
  | productive {jobL jobR : Job m outs} {store : σ}
      (run : ProductivePair primitives ids jobL jobR store) :
    CallPair primitives ids mapping outs ⟨Continuation.start jobL, store⟩ ⟨Continuation.start jobR, store⟩

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

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma
