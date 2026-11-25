module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence

open Execution
open Execution.Runtime (Value)
open OuterCall (coreValues)
open OuterCall.Computed

def Site.Resolves (site : Site) : Prop :=
  ∀ i : site.TargetId, site.frame.module.funcs[(site.target i).index.toNat]? = some (site.target i).address

structure V1Guard {H : Type} (s : Wasm.V1.Execution.Store H) (site : Site) : Prop where
  readOnly : site.ReadOnly
  typed : site.TypedTargets
  resolves : site.Resolves
  allocated : ∀ i : site.TargetId, s.funcs[(site.target i).address.value]? =
    some (.wasm (site.target i).callee.type (site.target i).callee.module (site.target i).callee.v1Func)

structure LimeGuard {H : Type} (s : Wasm.Lime1.Execution.Store H) (site : Site) : Prop where
  readOnly : site.ReadOnly
  typed : site.TypedTargets
  resolves : site.Resolves
  allocated : ∀ i : site.TargetId, s.funcs[(site.target i).address.value]? =
    some (.wasm (site.target i).callee.type (site.target i).callee.module (site.target i).callee.limeFunc)

structure CoreGuard {H : Type} (s : Core.Store H) (site : Site) : Prop where
  readOnly : site.ReadOnly
  typed : site.TypedTargets
  resolves : site.Resolves
  allocated : ∀ i : site.TargetId, s.funcs[(site.target i).address.value]? = some (site.target i).callee.coreInstance

def emit {A : Type} {site : Site} (ops : ArgumentSyntax A) : Op site → A
  | .numeric op => Prefix.emit ops op
  | .call i => ops.call (site.target i).index

def render {A : Type} (site : Site) (ops : ArgumentSyntax A) (values : List Value → List A)
    (trap : A) (callee : site.TargetId → CallFrame.State → List A) : State site → List A
  | .running stack rest => values stack ++ rest.map (emit ops)
  | .active i phase rest => callee i phase ++ rest.map (emit ops)
  | .trapped stack rest => values stack ++ trap :: rest.map (emit ops)

def v1Code (site : Site) : State site → List Wasm.V1.Execution.Admin :=
  render site v1Syntax Wasm.V1.Execution.values .trap
    (fun i => CallFrame.v1Code (site.target i).address (site.target i).callee)

def limeCode (site : Site) : State site → List Wasm.Lime1.Execution.Admin :=
  render site limeSyntax Wasm.Lime1.Execution.values .trap
    (fun i => CallFrame.limeCode (site.target i).address (site.target i).callee)

def coreCode (site : Site) : State site → List Core.Admin :=
  render site coreSyntax coreValues .trap
    (fun i => CallFrame.coreCode (site.target i).address (site.target i).callee)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (site : Site) (q : State site) :
    Wasm.V1.Execution.Config H := ⟨s, site.frame, v1Code site q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (site : Site) (q : State site) :
    Wasm.Lime1.Execution.Config H := ⟨s, site.frame, limeCode site q⟩

def coreConfig {H : Type} (s : Core.Store H) (site : Site) (q : State site) :
    Core.Config H := ⟨s, site.frame.toCore, coreCode site q⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence
