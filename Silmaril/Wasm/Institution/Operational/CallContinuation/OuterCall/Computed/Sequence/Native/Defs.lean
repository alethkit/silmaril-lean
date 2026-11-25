module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence

open Execution
open Execution.Runtime (Frame Value)

def Site.type (site : Site) : Wasm.V1.FuncType := ⟨site.params, site.inner.result.toList⟩

def Site.pendingOp {A : Type} (site : Site) (ops : ArgumentSyntax A) : Pending → A
  | .arg op => Prefix.emit ops op
  | .call => ops.call site.innerIndex
  | .nop => ops.nop

def Site.body {A : Type} (site : Site) (ops : ArgumentSyntax A) : List A :=
  (pending site.prefixCode).map (site.pendingOp ops)

def v1Source : ArgumentSyntax Wasm.V1.Instr :=
  ⟨Locals.v1Instr ∘ Locals.Op.value, .localGet, .intBinOp, .call, .nop⟩

def limeSource : ArgumentSyntax Wasm.Lime1.Instr :=
  ⟨Locals.limeInstr ∘ Locals.Op.value, .localGet, .intBinOp, .call, .nop⟩

def coreSource : ArgumentSyntax Wasm.Instr :=
  ⟨Locals.coreInstr ∘ Locals.Op.value, .localGet, .intBinOp, .call, .nop⟩

def Site.v1Func (site : Site) : Wasm.V1.Func :=
  ⟨site.typeIndex, site.locals, site.body v1Source⟩

def Site.limeFunc (site : Site) : Wasm.Lime1.Func :=
  ⟨site.typeIndex, site.locals, site.body limeSource⟩

def Site.coreFunc (site : Site) : Wasm.Func :=
  ⟨site.typeIndex, site.locals.map Wasm.V1.ValType.toCore, site.body coreSource⟩

def Site.coreInstance {H : Type} (site : Site) : Core.FuncInst H :=
  ⟨site.type.toDefType, site.outerModule.toCore, .wasm site.coreFunc⟩

structure NativeLookups (caller : Frame) (site : Site) : Prop where
  typed : Typed site
  outerLookup : caller.module.funcs[site.outerIndex.toNat]? = some site.outerAddr
  innerLookup : site.outerModule.funcs[site.innerIndex.toNat]? = some site.innerAddr

structure V1Guard {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site)
    : Prop extends NativeLookups caller site where
  outerAlloc : s.funcs[site.outerAddr.value]? = some (.wasm site.type site.outerModule site.v1Func)
  innerAlloc : s.funcs[site.innerAddr.value]? = some (.wasm site.inner.type site.inner.module site.inner.v1Func)

structure LimeGuard {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (site : Site)
    : Prop extends NativeLookups caller site where
  outerAlloc : s.funcs[site.outerAddr.value]? = some (.wasm site.type site.outerModule site.limeFunc)
  innerAlloc : s.funcs[site.innerAddr.value]? = some (.wasm site.inner.type site.inner.module site.inner.limeFunc)

structure CoreGuard {H : Type} (s : Core.Store H) (caller : Frame) (site : Site)
    : Prop extends NativeLookups caller site where
  outerAlloc : s.funcs[site.outerAddr.value]? = some site.coreInstance
  innerAlloc : s.funcs[site.innerAddr.value]? = some site.inner.coreInstance

def render {A : Type} (site : Site) (ops : ArgumentSyntax A) (values : List Value → List A)
    (trap : A) (wrap : List A → A) (call invoke : List A) (nested : Nested.State → List A) :
    State → List A
  | .call => call
  | .invoke => invoke
  | .args stack rest => [wrap (values stack ++ (pending rest).map (site.pendingOp ops))]
  | .trap stack rest => [wrap (values stack ++ trap :: rest.map (site.pendingOp ops))]
  | .nested phase => nested phase

def v1Code (site : Site) : State → List Wasm.V1.Execution.Admin :=
  render site v1Syntax Wasm.V1.Execution.values .trap
    (fun body => .frame site.arity site.frame [.label site.arity [] body])
    (Wasm.V1.Execution.values site.args ++ [.source (.call site.outerIndex)])
    (Wasm.V1.Execution.values site.args ++ [.invoke site.outerAddr])
    (Nested.v1Code site.frame site.innerAddr site.inner site.arity)

def limeCode (site : Site) : State → List Wasm.Lime1.Execution.Admin :=
  render site limeSyntax Wasm.Lime1.Execution.values .trap
    (fun body => .frame site.arity site.frame [.label site.arity [] body])
    (Wasm.Lime1.Execution.values site.args ++ [.source (.call site.outerIndex)])
    (Wasm.Lime1.Execution.values site.args ++ [.invoke site.outerAddr])
    (Nested.limeCode site.frame site.innerAddr site.inner site.arity)

def coreCode (site : Site) : State → List Core.Admin :=
  render site coreSyntax coreValues .trap
    (fun body => .frame site.arity site.frame.toCore [.label site.arity [] body])
    (coreValues site.args ++ [.plain (.call site.outerIndex)])
    (coreValues site.args ++ [.ref (.func site.outerAddr.value), .callRefType site.type.toDefType])
    (Nested.coreCode site.frame site.innerAddr site.inner site.arity)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site)
    (q : State) : Wasm.V1.Execution.Config H := ⟨s, caller, v1Code site q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (site : Site)
    (q : State) : Wasm.Lime1.Execution.Config H := ⟨s, caller, limeCode site q⟩

def coreConfig {H : Type} (s : Core.Store H) (caller : Frame) (site : Site)
    (q : State) : Core.Config H := ⟨s, caller.toCore, coreCode site q⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence
