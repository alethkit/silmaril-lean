module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall

open Silmaril.Formats Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Value

/-- A canonical component binding is nominally linked to a host function and to the
caller's guest memory. `async_` selects the reference ABI; this callee resolves eagerly. -/
structure Callee (sig : Signature) where
  name : String
  hostId : HostFuncId
  inst : InstId
  memory : Nat
  width : AddrType
  encoding : StringEncoding
  async_ : Bool
  tag : sig.Tag

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

def childrenType : TypeOf := .list (.prim .u32)

def resultType : TypeOf := .result (some (.prim .u32)) none

def Callee.funcType (callee : Callee sig) : WIT.FuncType Empty RtId :=
  ⟨[("children", childrenType), ("payload", sig.payload callee.tag)],
    some resultType, callee.async_⟩

def Callee.coreType (callee : Callee sig) : V1.FuncType :=
  ABI.flattenFunc { memory := callee.width, async_ := callee.async_ } .lower
    (.ofWIT callee.funcType)

def Callee.options (callee : Callee sig) : CanonOpts (core3 grow) :=
  { memory := some callee.memory, encoding := callee.encoding, async_ := callee.async_ }

/-- Link the Core import to the reference `canonLower`, not to the status-pair embedder
ABI. The host function at `function` must be installed at `callee.hostId`. -/
def Callee.lowered (callee : Callee sig) (function : FuncId) : CanonHost (core3 grow) :=
  .lowered function callee.funcType callee.options callee.inst

def Callee.check (callee : Callee sig) (store : CStore (core3 grow)) (subtask : SubtaskId)
    (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits : Nat × Nat) : Except Issue Unit := do
  if ft != callee.funcType then throw .wrongPayloadType
  if cx.inst != callee.inst || cx.scope != .subtask subtask then throw .wrongContext
  if cx.opts != callee.options || pos != 0 || limits != lowerLimits callee.async_ then
    throw .wrongPassingMode
  if (core3 grow).memAddrType? store.core callee.memory != some callee.width then
    throw .badLoweringMemory
  if !(store.subtask? subtask).any (fun entry =>
      entry.inst == callee.inst && entry.state == .starting && entry.index.isNone) then
    throw .wrongContext
  if args.map Stored.flatType != callee.coreType.params then throw .wrongType

/-- Read the non-owning first argument for checked child selection. Spilled arguments
share the alignment and whole-tuple range checks of `liftFlatValuesWith`. The first tuple
field is at offset zero. This read issues no host call or resource operation. -/
def readChildren (callee : Callee sig) (cx : LiftLowerContext (core3 grow))
    (args : List FlatValue) : P (core3 grow) Unit Val := do
  let width ← ptrType cx
  let cursor := FlatCursor.ofList args
  let types := callee.funcType.params.map (·.2)
  if (flattenTypes width types).length > (lowerLimits callee.async_).1 then
    let (ptr, _) ← cursor.next (pointerType width)
    let layout := ABI.layout width (.tuple types : TypeOf)
    trapIf (decide (flatNat ptr ≠ alignTo (flatNat ptr) layout.alignment)) .unalignedPointer
    checkInBounds cx (flatNat ptr) layout.size
    loadAt Limits.spec Quirks.none cx width childrenType (flatNat ptr)
  else
    Prod.fst <$> liftFlatAt Limits.spec Quirks.none cx width childrenType cursor

def selectChildren (callee : Callee sig) (history : List (Tree sig)) (value : Val) :
    Except Issue (List (Tree sig)) := do
  let .list ids := value | throw .wrongType
  if !(sig.arity callee.tag).Admits ids.length then
    throw (.accept (.boundary (.boundary .badArity)))
  ids.mapM fun value => do
    let .int .u32 index := value | throw .wrongType
    let handle := BitVec.ofNat 32 index.toNat
    let some tree := Endpoints.Core.childFromHistory history handle
      | throw (.accept (.boundary (.invalidChild handle)))
    return tree

def reject (ticket : Nat) (issue : Issue) : Session grow sig (Ret (core3 grow)) := do
  let _ ← rejectBinding ticket issue
  return .cancel .none

def planChildren (callee : Callee sig) (cx : LiftLowerContext (core3 grow))
    (args : List FlatValue) (store : CStore (core3 grow)) (history : List (Tree sig)) :
    Except Issue (Option (List (Tree sig))) :=
  match (Endpoints.Core.runLocal (readChildren callee cx args) store).2 with
  | .ok value => some <$> selectChildren callee history value
  | .error (.trapped _) => .ok none
  | .error issue => .error (.accept (.localEffect issue))

def resolveRefused (ticket : Nat) (caller : CallerId) (issue : Issue) :
    Session grow sig (Ret (core3 grow)) := do
  hostSet ((← hostGet).record (.refused ticket issue))
  lowerOnResolve Limits.spec Quirks.none caller (some [.variant 1 none])
  return .cancel .none

/-- With the exact flat signature already checked, the only result pointer is its final
word. A checked refusal can resolve the WIT error without lifting any of the payload.
This is intentionally not the reference removal-first path for a malformed payload. -/
def refuseBeforeLift (ticket : Nat) (caller : CallerId) (issue : Issue) :
    Session grow sig (Ret (core3 grow)) := do
  let _ ← lowerOnStartWith (fun _ _ cursor _ =>
    pure (([] : List Unit), { cursor with pos := cursor.values.length - 1 })) caller
  resolveRefused ticket caller issue

/-- Resolve first, then publish using the current writer. The result is non-allocating;
the commit still checks that the handle written by canonical resolution is the next
handle, and refuses rather than restoring a stale writer. -/
def resolveTree (ticket : Nat) (caller : CallerId) (tree : Tree sig) :
    Session grow sig (Ret (core3 grow)) := do
  let current ← hostGet
  let .ok writer := current.writer.register tree
    | resolveRefused ticket caller (.accept (.claims .alias))
  let handle := writer.accepted.length
  if handle ≥ 2 ^ 32 then return ← reject ticket (.accept (.boundary .exhaustedHandles))
  lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Val.u32 handle))])
  match ← publishRootAt ticket tree (some handle) with
  | .error issue => reject ticket issue
  | .ok published =>
    let _ ← writeCompletion (.returned ticket published, [])
    return .cancel .none

def invokeLower (callee : Callee sig) (caller : CallerId) (state : HostState sig)
    (subtask : SubtaskId) (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits results : Nat) : Session grow sig (Ret (core3 grow)) := do
  let ticket := state.nextTicket
  let store ← getStore
  if (← currentInst?) != some callee.inst then return ← reject ticket .wrongContext
  if let .error issue := callee.check store subtask cx args pos ft (limits, results) then
    return ← reject ticket issue
  if let .error issue := OwnedMemory.checkSchema (sig.payload callee.tag) then
    return ← refuseBeforeLift ticket caller (.accept (.claims (.lift (.schema issue))))
  if state.writer.accepted.length + 1 ≥ 2 ^ 32 then
    return ← refuseBeforeLift ticket caller (.accept (.boundary .exhaustedHandles))
  match planChildren callee cx args store state.writer.accepted with
  | .error issue => refuseBeforeLift ticket caller issue
  | .ok planned => do
    let [_, payload] ← observeLowerOnStart Limits.spec Quirks.none caller
      | reject ticket .wrongType
    let some children := planned | reject ticket .wrongType
    match OwnedMemory.checkValue (sig.payload callee.tag) payload with
    | .error issue => resolveRefused ticket caller (.accept (.claims (.lift issue)))
    | .ok payload => resolveTree ticket caller (AST.node callee.tag payload children)

def invoke (callee : Callee sig) (caller : CallerId) : Session grow sig (Ret (core3 grow)) := do
  let record ← getObj ArenaField.callers caller
  let state ← hostGet
  match record with
  | .lower subtask cx args pos ft limits results =>
    hostSet (state.enter callee.name callee.coreType args)
    invokeLower callee caller state subtask cx args pos ft limits results
  | _ =>
    hostSet (state.enter callee.name callee.coreType [])
    reject state.nextTicket .wrongContext

/-- Public dispatcher for canonical-lowered acceptor callees alongside existing checked
Core imports. Missing/ambiguous host function bindings fail with explicit diagnostics. -/
def hostWithComponent (bindings : List (Binding sig)) (callees : List (Callee sig)) :
    HostImpl (core3 grow) (HostState sig) :=
  { host bindings with funcs := fun id caller => do
    match callees.filter (·.hostId == id) with
    | [callee] => invoke callee caller
    | others =>
      let state ← hostGet
      hostSet (state.enter "component accept" ⟨[], []⟩ [])
      reject state.nextTicket (if others.isEmpty then .unlinkedImport else .ambiguousBinding) }

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall
