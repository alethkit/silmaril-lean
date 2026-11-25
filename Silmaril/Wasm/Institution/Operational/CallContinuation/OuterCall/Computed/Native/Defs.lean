module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed

open Execution
open Execution.Runtime (Frame Value)

def Site.type (site : Site) : Wasm.V1.FuncType := ⟨site.params, site.inner.result.toList⟩

/-- Only the prefix before `call; nop` is varied across computation phases. -/
structure ArgumentSyntax (A : Type) where
  value : Value → A
  get : LocalIdx → A
  binary : IntType → IntBinOp → A
  call : FuncIdx → A
  nop : A

def Site.suffix {A : Type} (site : Site) (ops : ArgumentSyntax A) : List A :=
  [ops.call site.innerIndex, ops.nop]

def Site.body {A : Type} (site : Site) (ops : ArgumentSyntax A) : List A :=
  [ops.get site.leftIndex, ops.get site.rightIndex, ops.binary site.kind site.op] ++ site.suffix ops

def Site.v1Func (site : Site) : Wasm.V1.Func :=
  ⟨site.typeIndex, site.locals, site.body ⟨Locals.v1Instr ∘ Locals.Op.value, .localGet, .intBinOp, .call, .nop⟩⟩

def Site.limeFunc (site : Site) : Wasm.Lime1.Func :=
  ⟨site.typeIndex, site.locals, site.body ⟨Locals.limeInstr ∘ Locals.Op.value, .localGet, .intBinOp, .call, .nop⟩⟩

def Site.coreFunc (site : Site) : Wasm.Func :=
  ⟨site.typeIndex, site.locals.map Wasm.V1.ValType.toCore,
    site.body ⟨Locals.coreInstr ∘ Locals.Op.value, .localGet, .intBinOp, .call, .nop⟩⟩

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

def v1Syntax : ArgumentSyntax Wasm.V1.Execution.Admin :=
  ⟨Wasm.V1.Execution.value, .source ∘ .localGet, fun t o => .source (.intBinOp t o), .source ∘ .call, .source .nop⟩

def limeSyntax : ArgumentSyntax Wasm.Lime1.Execution.Admin :=
  ⟨Wasm.Lime1.Execution.value, .source ∘ .localGet, fun t o => .source (.intBinOp t o), .source ∘ .call, .source .nop⟩

def coreSyntax : ArgumentSyntax Core.Admin :=
  ⟨fun v => v.toCore.toAdmin, .plain ∘ .localGet, fun t o => .plain (.intBinOp t o), .plain ∘ .call, .plain .nop⟩

def render {A : Type} (site : Site) (ops : ArgumentSyntax A) (trap : A)
    (wrap : List A → A) (call invoke : List A) (nested : Nested.State → List A) :
    State site → List A
  | .call => call
  | .invoke => invoke
  | .readLeft => [wrap (site.body ops)]
  | .readRight => [wrap ([ops.value (.int site.kind site.left), ops.get site.rightIndex,
      ops.binary site.kind site.op] ++ site.suffix ops)]
  | .compute => [wrap ([ops.value (.int site.kind site.left), ops.value (.int site.kind site.right),
      ops.binary site.kind site.op] ++ site.suffix ops)]
  | .argument bits => [wrap (ops.value (.int site.kind bits) :: site.suffix ops)]
  | .argumentTrap => [wrap (trap :: site.suffix ops)]
  | .nested phase => nested phase

def v1Code (site : Site) : State site → List Wasm.V1.Execution.Admin :=
  render site v1Syntax .trap (fun body => .frame site.arity site.frame [.label site.arity [] body])
    (Wasm.V1.Execution.values site.args ++ [.source (.call site.outerIndex)])
    (Wasm.V1.Execution.values site.args ++ [.invoke site.outerAddr])
    (Nested.v1Code site.frame site.innerAddr site.inner site.arity)

def limeCode (site : Site) : State site → List Wasm.Lime1.Execution.Admin :=
  render site limeSyntax .trap (fun body => .frame site.arity site.frame [.label site.arity [] body])
    (Wasm.Lime1.Execution.values site.args ++ [.source (.call site.outerIndex)])
    (Wasm.Lime1.Execution.values site.args ++ [.invoke site.outerAddr])
    (Nested.limeCode site.frame site.innerAddr site.inner site.arity)

def coreCode (site : Site) : State site → List Core.Admin :=
  render site coreSyntax .trap (fun body => .frame site.arity site.frame.toCore [.label site.arity [] body])
    (coreValues site.args ++ [.plain (.call site.outerIndex)])
    (coreValues site.args ++ [.ref (.func site.outerAddr.value), .callRefType site.type.toDefType])
    (Nested.coreCode site.frame site.innerAddr site.inner site.arity)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site)
    (q : State site) : Wasm.V1.Execution.Config H := ⟨s, caller, v1Code site q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (site : Site)
    (q : State site) : Wasm.Lime1.Execution.Config H := ⟨s, caller, limeCode site q⟩

def coreConfig {H : Type} (s : Core.Store H) (caller : Frame) (site : Site)
    (q : State site) : Core.Config H := ⟨s, caller.toCore, coreCode site q⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed
