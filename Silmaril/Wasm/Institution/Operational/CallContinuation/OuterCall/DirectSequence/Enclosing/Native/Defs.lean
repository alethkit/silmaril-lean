module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing

open Execution
open Execution.Runtime (Value)
open Computed (v1Syntax limeSyntax coreSyntax)
open StraightLine

structure V1Guard {H : Type} (s : Wasm.V1.Execution.Store H) (ctx : Context) (p : Program) : Prop where
  invocation : DirectSequence.V1Guard s ctx.frame p
  continuation : Sequence.V1Guard s ctx.sequence

structure LimeGuard {H : Type} (s : Wasm.Lime1.Execution.Store H) (ctx : Context) (p : Program) : Prop where
  invocation : DirectSequence.LimeGuard s ctx.frame p
  continuation : Sequence.LimeGuard s ctx.sequence

structure CoreGuard {H : Type} (s : Core.Store H) (ctx : Context) (p : Program) : Prop where
  invocation : DirectSequence.CoreGuard s ctx.frame p
  continuation : Sequence.CoreGuard s ctx.sequence

def render {A : Type} {ctx : Context} {site : Site} (values : List Value → List A)
    (body : DirectSequence.State site → List A) (tail : List A) (suffix : Sequence.State ctx.sequence → List A) :
    State ctx site → List A
  | .active q => values ctx.saved ++ body q ++ tail
  | .continuation q => suffix q

def v1Code (ctx : Context) (site : Site) : State ctx site → List Wasm.V1.Execution.Admin :=
  render Wasm.V1.Execution.values (DirectSequence.v1Code site) (ctx.continuation.map (Sequence.emit v1Syntax))
    (Sequence.v1Code ctx.sequence)

def limeCode (ctx : Context) (site : Site) : State ctx site → List Wasm.Lime1.Execution.Admin :=
  render Wasm.Lime1.Execution.values (DirectSequence.limeCode site) (ctx.continuation.map (Sequence.emit limeSyntax))
    (Sequence.limeCode ctx.sequence)

def coreCode (ctx : Context) (site : Site) : State ctx site → List Core.Admin :=
  render coreValues (DirectSequence.coreCode site) (ctx.continuation.map (Sequence.emit coreSyntax))
    (Sequence.coreCode ctx.sequence)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (ctx : Context) (site : Site) (q : State ctx site) :
    Wasm.V1.Execution.Config H := ⟨s, ctx.frame, v1Code ctx site q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (ctx : Context) (site : Site) (q : State ctx site) :
    Wasm.Lime1.Execution.Config H := ⟨s, ctx.frame, limeCode ctx site q⟩

def coreConfig {H : Type} (s : Core.Store H) (ctx : Context) (site : Site) (q : State ctx site) :
    Core.Config H := ⟨s, ctx.frame.toCore, coreCode ctx site q⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing
