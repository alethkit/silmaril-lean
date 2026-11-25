module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine

open Execution
open Execution.Runtime (Frame Value)
open OuterCall (coreValues)
open OuterCall.Computed

/-- Common allocation and index premises for the entered outer frame. -/
def Site.Lookup (site : Site) : Prop :=
  site.outer.module.funcs[site.index.toNat]? = some site.address

structure V1Guard {H : Type} (s : Wasm.V1.Execution.Store H) (site : Site) : Prop where
  lookup : site.Lookup
  allocated : s.funcs[site.address.value]? = some (.wasm site.callee.type site.callee.module site.callee.v1Func)

structure LimeGuard {H : Type} (s : Wasm.Lime1.Execution.Store H) (site : Site) : Prop where
  lookup : site.Lookup
  allocated : s.funcs[site.address.value]? = some (.wasm site.callee.type site.callee.module site.callee.limeFunc)

structure CoreGuard {H : Type} (s : Core.Store H) (site : Site) : Prop where
  lookup : site.Lookup
  allocated : s.funcs[site.address.value]? = some site.callee.coreInstance

def renderBody {A : Type} (site : Site) (ops : ArgumentSyntax A) (values : List Value → List A)
    (trap : A) (callee : CallFrame.State → List A) : State → List A
  | .call saved args => values (saved ++ args) ++ ops.call site.index :: site.continuation.map (Prefix.emit ops)
  | .active q => callee q ++ site.continuation.map (Prefix.emit ops)
  | .resume stack rest => values stack ++ rest.map (Prefix.emit ops)
  | .trapped stack rest => values stack ++ trap :: rest.map (Prefix.emit ops)
  | .boundary _ => []

def render {A : Type} (wrap : List A → A) (body : State → List A) (boundary : Nested.State → List A) :
    State → List A
  | .boundary q => boundary q
  | q => [wrap (body q)]

def v1Body (site : Site) : State → List Wasm.V1.Execution.Admin :=
  renderBody site v1Syntax Wasm.V1.Execution.values .trap (CallFrame.v1Code site.address site.callee)

def limeBody (site : Site) : State → List Wasm.Lime1.Execution.Admin :=
  renderBody site limeSyntax Wasm.Lime1.Execution.values .trap (CallFrame.limeCode site.address site.callee)

def coreBody (site : Site) : State → List Core.Admin :=
  renderBody site coreSyntax coreValues .trap (CallFrame.coreCode site.address site.callee)

def v1Code (site : Site) : State → List Wasm.V1.Execution.Admin :=
  render (fun body => .frame site.arity site.outer [.label site.arity [] body])
    (v1Body site) (Nested.v1Code site.outer site.address site.callee site.arity)

def limeCode (site : Site) : State → List Wasm.Lime1.Execution.Admin :=
  render (fun body => .frame site.arity site.outer [.label site.arity [] body])
    (limeBody site) (Nested.limeCode site.outer site.address site.callee site.arity)

def coreCode (site : Site) : State → List Core.Admin :=
  render (fun body => .frame site.arity site.outer.toCore [.label site.arity [] body])
    (coreBody site) (Nested.coreCode site.outer site.address site.callee site.arity)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site)
    (q : State) : Wasm.V1.Execution.Config H := ⟨s, caller, v1Code site q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (site : Site)
    (q : State) : Wasm.Lime1.Execution.Config H := ⟨s, caller, limeCode site q⟩

def coreConfig {H : Type} (s : Core.Store H) (caller : Frame) (site : Site)
    (q : State) : Core.Config H := ⟨s, caller.toCore, coreCode site q⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine
