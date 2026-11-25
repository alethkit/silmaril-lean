module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed

open Execution
open Execution.Runtime (Frame Value)

def Site.type (site : Site) : Wasm.V1.FuncType := ⟨site.params, site.result.toList⟩

def Site.emit {A : Type} (site : Site) (ops : ArgumentSyntax A) : Pending → A
  | .op op => Prefix.emit ops op
  | .call => ops.call site.innerIndex

def Site.body {A : Type} (site : Site) (ops : ArgumentSyntax A) : List A :=
  (site.pending site.prefixCode).map (site.emit ops)

def Site.v1Func (site : Site) : Wasm.V1.Func :=
  ⟨site.typeIndex, site.locals, site.body v1Source⟩

def Site.limeFunc (site : Site) : Wasm.Lime1.Func :=
  ⟨site.typeIndex, site.locals, site.body limeSource⟩

def Site.coreFunc (site : Site) : Wasm.Func :=
  ⟨site.typeIndex, site.locals.map Wasm.V1.ValType.toCore, site.body coreSource⟩

def Site.coreInstance {H : Type} (site : Site) : Core.FuncInst H :=
  ⟨site.type.toDefType, site.outerModule.toCore, .wasm site.coreFunc⟩

structure Lookups (caller : Frame) (site : Site) : Prop where
  typed : Typed site
  outerLookup : caller.module.funcs[site.outerIndex.toNat]? = some site.outerAddr

structure V1Guard {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site)
    : Prop extends Lookups caller site where
  outerAlloc : s.funcs[site.outerAddr.value]? = some (.wasm site.type site.outerModule site.v1Func)
  innerGuard : StraightLine.V1Guard s site.innerSite

structure LimeGuard {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (site : Site)
    : Prop extends Lookups caller site where
  outerAlloc : s.funcs[site.outerAddr.value]? = some (.wasm site.type site.outerModule site.limeFunc)
  innerGuard : StraightLine.LimeGuard s site.innerSite

structure CoreGuard {H : Type} (s : Core.Store H) (caller : Frame) (site : Site)
    : Prop extends Lookups caller site where
  outerAlloc : s.funcs[site.outerAddr.value]? = some site.coreInstance
  innerGuard : StraightLine.CoreGuard s site.innerSite

def render {A : Type} (site : Site) (ops : ArgumentSyntax A)
    (values : List Value → List A) (trap : A) (wrap : List A → A)
    (call invoke : List A) (inner : StraightLine.State → List A) : State → List A
  | .call => call
  | .invoke => invoke
  | .args stack remaining => [wrap (values stack ++ (site.pending remaining).map (site.emit ops))]
  | .argumentTrap stack remaining => [wrap (values stack ++ trap :: remaining.map (site.emit ops))]
  | .inner phase => inner phase

def v1Code (site : Site) : State → List Wasm.V1.Execution.Admin :=
  render site v1Syntax Wasm.V1.Execution.values .trap
    (fun body => .frame site.innerSite.arity site.toSite.frame [.label site.innerSite.arity [] body])
    (Wasm.V1.Execution.values site.args ++ [.source (.call site.outerIndex)])
    (Wasm.V1.Execution.values site.args ++ [.invoke site.outerAddr])
    (StraightLine.v1Code site.innerSite)

def limeCode (site : Site) : State → List Wasm.Lime1.Execution.Admin :=
  render site limeSyntax Wasm.Lime1.Execution.values .trap
    (fun body => .frame site.innerSite.arity site.toSite.frame [.label site.innerSite.arity [] body])
    (Wasm.Lime1.Execution.values site.args ++ [.source (.call site.outerIndex)])
    (Wasm.Lime1.Execution.values site.args ++ [.invoke site.outerAddr])
    (StraightLine.limeCode site.innerSite)

def coreCode (site : Site) : State → List Core.Admin :=
  render site coreSyntax coreValues .trap
    (fun body => .frame site.innerSite.arity site.toSite.frame.toCore [.label site.innerSite.arity [] body])
    (coreValues site.args ++ [.plain (.call site.outerIndex)])
    (coreValues site.args ++ [.ref (.func site.outerAddr.value), .callRefType site.type.toDefType])
    (StraightLine.coreCode site.innerSite)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site)
    (q : State) : Wasm.V1.Execution.Config H := ⟨s, caller, v1Code site q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (site : Site)
    (q : State) : Wasm.Lime1.Execution.Config H := ⟨s, caller, limeCode site q⟩

def coreConfig {H : Type} (s : Core.Store H) (caller : Frame) (site : Site)
    (q : State) : Core.Config H := ⟨s, caller.toCore, coreCode site q⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed
