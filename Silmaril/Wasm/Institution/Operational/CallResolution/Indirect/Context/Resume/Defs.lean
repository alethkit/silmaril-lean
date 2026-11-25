module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume

open Execution
open Execution.Runtime (Frame FuncAddr Value)
open CallContinuation
open CallContinuation.OuterCall (CallTarget)
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

/-- A parameterless scalar block and its continuation in the enclosing label. -/
structure Block where
  result : Option NumType
  tail : List Graph.Op

def Block.scope (block : Block) (saved : List Value) : Blocks.Context.Scope Graph.Op :=
  ⟨block.result.toList.length, saved, block.tail⟩

/-- The scopes are outermost first. Each parameterless entry starts the
next block with an empty operand stack. -/
def Block.scopes : List Block → List Value → List (Blocks.Context.Scope Graph.Op)
  | [], _ => []
  | block :: rest, saved => block.scope saved :: scopes rest []

def Block.context : List Block → List NumType → Graph.EnclosingLabels → List NumType × Graph.EnclosingLabels
  | [], fallthrough, enclosing => (fallthrough, enclosing)
  | block :: rest, fallthrough, enclosing => context rest block.result.toList (fallthrough :: enclosing)

def Block.check (fn : Graph.Function) : List Block → List Value → List NumType → Graph.EnclosingLabels → Bool
  | [], _, _, _ => true
  | block :: rest, saved, fallthrough, enclosing =>
      check fn rest [] block.result.toList (fallthrough :: enclosing) &&
      Graph.checkCode fn.targets fn.localTypes fn.declaration.results fallthrough enclosing
        (block.result.toList.reverse ++ Prefix.stackTypes saved) block.tail .exit fn.declaration.module.types

def Block.plug : List Block → List Value → Graph.Body → Graph.Body
  | [], _, body => body
  | block :: rest, saved, body => .block saved block.result (plug rest [] body) block.tail

/-- A designated call site under a spine of immediately nested parameterless
scalar blocks, ordered outermost first. The outermost block saves the
function's initial operands. -/
structure Continuation where
  address : FuncAddr
  owner : Graph.Function
  code : List Graph.Op
  blocks : List Block := []

def Continuation.scopes (cont : Continuation) : List (Blocks.Context.Scope Graph.Op) :=
  Block.scopes cont.blocks cont.owner.initial

def Continuation.fallthrough (cont : Continuation) : List NumType :=
  (Block.context cont.blocks cont.owner.declaration.results []).1

def Continuation.enclosing (cont : Continuation) : Graph.EnclosingLabels :=
  (Block.context cont.blocks cont.owner.declaration.results []).2

def Continuation.blockCheck (cont : Continuation) : Bool :=
  Block.check cont.owner cont.blocks cont.owner.initial cont.owner.declaration.results []

def Continuation.plug (cont : Continuation) (body : Graph.Body) : Graph.Body :=
  Block.plug cont.blocks cont.owner.initial body

structure Continuation.Checked (cont : Continuation) (program : Graph.Program)
    (caller : Frame) (saved : List Value) (results : List NumType) : Prop where
  found : program.lookup cont.address = some cont.owner
  module_eq : caller.module = cont.owner.declaration.module
  locals_typed : caller.locals.map Value.type = cont.owner.localTypes
  tail_typed : Graph.checkCode cont.owner.targets cont.owner.localTypes cont.owner.declaration.results
    cont.fallthrough cont.enclosing (results.reverse ++ Prefix.stackTypes saved)
    cont.code .exit cont.owner.declaration.module.types = true
  block_typed : cont.blockCheck = true

/-- The caller activation has already entered, so no direct index is needed to
render it. Its own direct targets are still checked by the graph. -/
def Continuation.target (cont : Continuation) : CallTarget :=
  ⟨⟨0⟩, cont.address, cont.owner.declaration⟩

def Continuation.deliver (cont : Continuation) (saved : List Value) : Nested.Result → Graph.Body
  | .values xs => .running (saved ++ xs) cont.code
  | .trap => .trapped saved cont.code

def Continuation.resume (cont : Continuation) (caller : Frame) (saved : List Value)
    (result : Nested.Result) : Graph.Phase :=
  .label caller.locals (cont.plug (cont.deliver saved result))

/-- The phase records which existing frame relation owns the next native step. -/
inductive Phase
  | callee (phase : Graph.Phase)
  | caller (phase : Graph.Phase)

/-- The frame exit delivers the outcome in one native step. The first step
from the delivered outcome is already a step of the checked caller. -/
inductive Edge (program : Graph.Program) (call : Invocation) (cont : Continuation) : Phase → Phase → Prop
  | callee {a b} (live : a.LabelOutcome) (move : program.FrameEdge call.address a b) :
      Edge program call cont (.callee a) (.callee b)
  | resume {result b} (move : program.FrameEdge cont.address (cont.resume call.caller call.saved result) b) :
      Edge program call cont (.callee (.done result)) (.caller b)
  | caller {a b} (move : program.FrameEdge cont.address a b) :
      Edge program call cont (.caller a) (.caller b)

abbrev Runs (program : Graph.Program) (call : Invocation) (cont : Continuation) :=
  Relation.ReflTransGen (Edge program call cont)

def Continuation.coreWrap {H : Type} (cont : Continuation) (outer : Frame) (body : Core.Config H) : Core.Config H :=
  let n := cont.owner.declaration.results.length
  ⟨body.store, outer.toCore, [.frame n body.frame [.label n [] body.code]]⟩

def Continuation.limeWrap {H : Type} (cont : Continuation) (outer : Frame)
    (body : Wasm.Lime1.Execution.Config H) : Wasm.Lime1.Execution.Config H :=
  let n := cont.owner.declaration.results.length
  ⟨body.store, outer, [.frame n body.frame [.label n [] body.code]]⟩

def Continuation.coreSiteWrap {H : Type} (cont : Continuation) (outer : Frame)
    (body : Core.Config H) : Core.Config H :=
  cont.coreWrap outer (coreNest cont.scopes body)

def Continuation.limeSiteWrap {H : Type} (cont : Continuation) (outer : Frame)
    (body : Wasm.Lime1.Execution.Config H) : Wasm.Lime1.Execution.Config H :=
  cont.limeWrap outer (limeNest cont.scopes body)

def Continuation.coreConfig {H : Type} (cont : Continuation) (call : Invocation)
    (s : Core.Store H) (outer : Frame) : Phase → Core.Config H
  | .callee phase => cont.coreSiteWrap outer (call.coreCallee s (cont.code.map Graph.coreEmit) phase)
  | .caller phase => Graph.coreConfig s outer cont.target phase

def Continuation.limeConfig {H : Type} (cont : Continuation) (call : Invocation)
    (s : Wasm.Lime1.Execution.Store H) (outer : Frame) : Phase → Wasm.Lime1.Execution.Config H
  | .callee phase => cont.limeSiteWrap outer (call.limeCallee s (cont.code.map Graph.limeEmit) phase)
  | .caller phase => Graph.limeConfig s outer cont.target phase

def Continuation.corePrefix {H : Type} (cont : Continuation) (call : Invocation)
    (s : Core.Store H) (outer : Frame) : List (Core.Config H) :=
  (call.corePrefix s (cont.code.map Graph.coreEmit)).map (cont.coreSiteWrap outer)

def Continuation.limePrefix {H : Type} (cont : Continuation) (call : Invocation)
    (s : Wasm.Lime1.Execution.Store H) (outer : Frame) : List (Wasm.Lime1.Execution.Config H) :=
  (call.limePrefix s (cont.code.map Graph.limeEmit)).map (cont.limeSiteWrap outer)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume
