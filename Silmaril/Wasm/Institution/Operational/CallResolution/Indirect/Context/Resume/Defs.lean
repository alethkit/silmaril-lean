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

/-- One designated call site in an entered function label has this checked tail.
The activation's locals and saved operands belong to the concrete invocation. -/
structure Continuation where
  address : FuncAddr
  owner : Graph.Function
  code : List Graph.Op

structure Continuation.Checked (cont : Continuation) (program : Graph.Program)
    (caller : Frame) (saved : List Value) (results : List NumType) : Prop where
  found : program.lookup cont.address = some cont.owner
  module_eq : caller.module = cont.owner.declaration.module
  locals_typed : caller.locals.map Value.type = cont.owner.localTypes
  tail_typed : Graph.checkCode cont.owner.targets cont.owner.localTypes cont.owner.declaration.results
    cont.owner.declaration.results [] (results.reverse ++ Prefix.stackTypes saved)
    cont.code .exit cont.owner.declaration.module.types = true

/-- The caller activation has already entered, so no direct index is needed to
render it. Its own direct targets are still checked by the graph. -/
def Continuation.target (cont : Continuation) : CallTarget :=
  ⟨⟨0⟩, cont.address, cont.owner.declaration⟩

def Continuation.resume (cont : Continuation) (caller : Frame) (saved : List Value)
    (result : Nested.Result) : Graph.Phase :=
  .label caller.locals <| match result with
    | .values xs => .running (saved ++ xs) cont.code
    | .trap => .trapped saved cont.code

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

def Continuation.coreConfig {H : Type} (cont : Continuation) (call : Invocation)
    (s : Core.Store H) (outer : Frame) : Phase → Core.Config H
  | .callee phase => cont.coreWrap outer (call.coreCallee s (cont.code.map Graph.coreEmit) phase)
  | .caller phase => Graph.coreConfig s outer cont.target phase

def Continuation.limeConfig {H : Type} (cont : Continuation) (call : Invocation)
    (s : Wasm.Lime1.Execution.Store H) (outer : Frame) : Phase → Wasm.Lime1.Execution.Config H
  | .callee phase => cont.limeWrap outer (call.limeCallee s (cont.code.map Graph.limeEmit) phase)
  | .caller phase => Graph.limeConfig s outer cont.target phase

def Continuation.corePrefix {H : Type} (cont : Continuation) (call : Invocation)
    (s : Core.Store H) (outer : Frame) : List (Core.Config H) :=
  (call.corePrefix s (cont.code.map Graph.coreEmit)).map (cont.coreWrap outer)

def Continuation.limePrefix {H : Type} (cont : Continuation) (call : Invocation)
    (s : Wasm.Lime1.Execution.Store H) (outer : Frame) : List (Wasm.Lime1.Execution.Config H) :=
  (call.limePrefix s (cont.code.map Graph.limeEmit)).map (cont.limeWrap outer)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume
