module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed

open Execution
open Execution.Runtime (Frame)

def render {A : Type} {ctx : Context} {site : Site} (frame label : List A → A)
    (body : Enclosing.State ctx site → List A) (result : Nested.Result → List A) : State ctx site → List A
  | .label q => [frame [label (body q)]]
  | .exit r => [frame (result r)]
  | .done r => result r

def v1Code (ctx : Context) (site : Site) : State ctx site → List Wasm.V1.Execution.Admin :=
  render (.frame ctx.sequence.results.length ctx.frame) (.label ctx.sequence.results.length [])
    (Enclosing.v1Code ctx site) (Nested.resultCode Wasm.V1.Execution.values .trap)

def limeCode (ctx : Context) (site : Site) : State ctx site → List Wasm.Lime1.Execution.Admin :=
  render (.frame ctx.sequence.results.length ctx.frame) (.label ctx.sequence.results.length [])
    (Enclosing.limeCode ctx site) (Nested.resultCode Wasm.Lime1.Execution.values .trap)

def coreCode (ctx : Context) (site : Site) : State ctx site → List Core.Admin :=
  render (.frame ctx.sequence.results.length ctx.frame.toCore) (.label ctx.sequence.results.length [])
    (Enclosing.coreCode ctx site) (Nested.resultCode coreValues .trap)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (ctx : Context) (site : Site)
    (q : State ctx site) : Wasm.V1.Execution.Config H := ⟨s, caller, v1Code ctx site q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (ctx : Context) (site : Site)
    (q : State ctx site) : Wasm.Lime1.Execution.Config H := ⟨s, caller, limeCode ctx site q⟩

def coreConfig {H : Type} (s : Core.Store H) (caller : Frame) (ctx : Context) (site : Site)
    (q : State ctx site) : Core.Config H := ⟨s, caller.toCore, coreCode ctx site q⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed
