module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing

open Execution
open Execution.Runtime (Value)
open Computed (ArgumentSyntax v1Syntax limeSyntax coreSyntax)

def render {A : Type} {site : Site} (ctx : Context) (ops : ArgumentSyntax A)
    (values : List Value → List A) (trap : A) (body : DirectSequence.State site → List A) : State site → List A
  | .active q => values ctx.saved ++ body q ++ ctx.continuation.map (Computed.Prefix.emit ops)
  | .resume stack rest => values stack ++ rest.map (Computed.Prefix.emit ops)
  | .trapped stack rest => values stack ++ trap :: rest.map (Computed.Prefix.emit ops)

def v1Code (ctx : Context) (site : Site) : State site → List Wasm.V1.Execution.Admin :=
  render ctx v1Syntax Wasm.V1.Execution.values .trap (DirectSequence.v1Code site)

def limeCode (ctx : Context) (site : Site) : State site → List Wasm.Lime1.Execution.Admin :=
  render ctx limeSyntax Wasm.Lime1.Execution.values .trap (DirectSequence.limeCode site)

def coreCode (ctx : Context) (site : Site) : State site → List Core.Admin :=
  render ctx coreSyntax coreValues .trap (DirectSequence.coreCode site)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (ctx : Context) (site : Site) (q : State site) :
    Wasm.V1.Execution.Config H := ⟨s, ctx.frame, v1Code ctx site q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (ctx : Context) (site : Site) (q : State site) :
    Wasm.Lime1.Execution.Config H := ⟨s, ctx.frame, limeCode ctx site q⟩

def coreConfig {H : Type} (s : Core.Store H) (ctx : Context) (site : Site) (q : State site) :
    Core.Config H := ⟨s, ctx.frame.toCore, coreCode ctx site q⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing
