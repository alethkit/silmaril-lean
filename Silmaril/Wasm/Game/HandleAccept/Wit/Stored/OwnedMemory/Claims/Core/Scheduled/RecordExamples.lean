module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
meta import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
meta import Silmaril.Wasm.Component.Reference.Machine.Exec.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.RecordExamples

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core

public abbrev grow := SingleThreaded.neverFail
public abbrev engine := core3 grow
@[expose] public def resource : RtId := ⟨0⟩
@[expose] public def element : Option (WIT.ClosedType RtId) := some (.prim .u16)
@[expose] public def signature : Signature := ⟨Unit, fun _ => .record [
  ("owners", .fixedList (.own resource) 2), ("reader", .option (.stream element))], fun _ => .fixed 0⟩
private def contract : Endpoints.Core.Contract signature :=
  ⟨0, ("host", "accept-node"), (fun tag => if tag == 0 then some () else none), {}, ⟨0⟩⟩

private def wordFn (params results : Nat) : V1.FuncType :=
  ⟨List.replicate params (.int .i32), List.replicate results (.int .i32)⟩

private def imports : List (String × V1.FuncType × CanonHost engine) :=
  let accept := Endpoints.Core.Scheduled.acceptType contract
  [("accept-node", accept, .embedder "accept-node" accept),
    ("give-record", wordFn 2 2, .embedder "give-record" (wordFn 2 2)),
    ("bad-memory", wordFn 2 2, .embedder "bad-memory" (wordFn 2 2)),
    ("bad-realloc", wordFn 2 2, .embedder "bad-realloc" (wordFn 2 2)),
    ("new-own", wordFn 1 1, .builtin (.resourceNew resource .i32) ⟨0⟩),
    ("new-stream", ⟨[], [.int .i64]⟩, .builtin (.streamNew element) ⟨0⟩),
    ("rep", wordFn 1 1, .builtin (.resourceRep resource .i32) ⟨0⟩),
    ("close-reader", wordFn 1 0, .builtin (.streamDropReadable element) ⟨0⟩),
    ("close-writer", wordFn 1 0, .builtin (.streamDropWritable element) ⟨0⟩)]

private def indexOf {kind : IndexKind} (index : Nat) : Idx kind := ⟨Fin.ofNat _ index⟩
private def word (value : Nat) : Instr := .intConst .i32 (BitVec.ofNat 32 value)
private def storeWord (ptr value : Nat) : List Instr :=
  [word ptr, word value, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩]

private def instantiate : Option (Store (CanonHost engine) × ModuleInst) := do
  let (store, addrs) := imports.foldl (fun (store, addresses) (_, type, code) =>
    let (next, addr) := SingleThreaded.allocHost store type code
    (next, addresses ++ [ExternAddr.func addr])) ({}, [])
  let names := imports.map (·.1)
  let wrapper := fun index =>
    let params := (imports[index]?.map (·.2.1.params.length)).getD 0
    let setup := if index == 0 then
      storeWord 32 1 ++ storeWord 36 2 ++ storeWord 40 1 ++ storeWord 44 3 else []
    (⟨indexOf index, [], setup ++ (List.range params).map (fun param => .localGet (indexOf param)) ++
      [.call (indexOf index)]⟩ : Func)
  let module_ : Module := {
    types := imports.map (·.2.1.toCoreRec)
    imports := names.zipIdx |>.map fun (name, index) => ⟨"host", name, .func (indexOf index)⟩
    memories := [⟨.i32, ⟨1, none⟩⟩]
    funcs := (List.range names.length).map wrapper
    exports := names.zipIdx |>.map fun (name, index) => ⟨name, .func (indexOf (index + names.length))⟩ }
  let (store, inst, none) ← Core3.prepareE? store module_ addrs | none
  return (store, inst)

private def exportAddr (inst : ModuleInst) (name : String) : Option engine.FuncAddr := do
  let (_, .func address) ← (Core3.instExports inst).find? (·.1 == name) | none
  return address

private def session (inst : ModuleInst) : Session grow signature (Ret engine) := do
  let run (name : String) (args : List Nat) (expected : List FlatValue) := do
    let some addr := exportAddr inst name | internal s!"missing Core export {name}"
    trapIf ((← callCore addr (args.map i32Flat)) != expected) (.internal s!"unexpected result: {name}")
  let refused := [i32Flat 1, i32Flat 0]
  let success (value : Nat) := [i32Flat 0, i32Flat value]
  run "new-own" [77] [i32Flat 1]
  run "new-own" [77] [i32Flat 2]
  run "new-stream" [] [.int .i64 (BitVec.ofNat 64 (packEnds 3 4))]
  run "accept-node" [0, 32, 0, 0] (success 1)
  run "bad-memory" [1, 0] refused
  run "bad-realloc" [1, 0] refused
  run "give-record" [1, 0] (success 0)
  run "give-record" [1, 0] refused
  run "rep" [3] [i32Flat 77]
  run "rep" [2] [i32Flat 77]
  run "accept-node" [0, 0, 0, 0] (success 2)
  run "give-record" [1, 0] refused
  run "give-record" [2, 16] (success 0)
  run "close-reader" [3] []
  run "close-writer" [4] []
  return .unit

private def ready : HostReady (HostState signature) := fun _ _ => false

private def setup : Option (List (Binding signature) × Machine.Config engine (HostState signature)) := do
  let (store, inst) ← instantiate
  let .ok lower := Binding.giveRecord "give-record" ⟨0⟩ inst 0 .i32 .utf8 | none
  let .ok badRealloc := Binding.giveRecord "bad-realloc" ⟨0⟩ inst 0 .i32 .utf8 (some 0) | none
  let bindings := [Binding.accept contract inst 0, lower, badRealloc,
    ⟨"bad-memory", ⟨0⟩, .giveRecord ⟨99, .i32, none, .utf8⟩⟩]
  let reference : CStore engine := { CStore.empty with
    core := store, insts := [{}], resourceTypes := [{ impl := some ⟨0⟩ }],
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }],
    threads := [{ status := .running, task := ⟨0⟩ }] }
  return (bindings, {
    store := reference, host := {}, conts := [none]
    ctl := [Machine.Activation.ofProg (some ⟨0⟩) (session inst)] })

private def run (bindings : List (Binding signature)) (config : Machine.Config engine (HostState signature)) :=
  Machine.run ready (specDispatch ready (host bindings)) (core3Exec grow) Machine.Oracle.first 1500 config

private theorem run_sound (bindings : List (Binding signature)) (config : Machine.Config engine (HostState signature)) :
    Machine.Steps .deterministic ready (specDispatch ready (host bindings)) config
      (run bindings config).labels (run bindings config).config :=
  Machine.run_sound ready (specDispatch ready (host bindings)) (core3Exec grow) Machine.Oracle.first 1500 config

private def regression : Bool :=
  match setup with
  | none => false
  | some (bindings, config) =>
    let result := run bindings config
    let writer := result.config.host.writer
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    let spent := Issue.lowerRecord (.claims .unclaimed)
    let accept := fun ticket ptr => Event.entered ticket "accept-node"
      (Endpoints.Core.Scheduled.acceptType contract) [i32Flat 0, i32Flat ptr, i32Flat 0, i32Flat 0]
    let give := fun ticket name handle ptr => Event.entered ticket name (wordFn 2 2) [i32Flat handle, i32Flat ptr]
    result.outcome == .resolved && writer.held.isEmpty && writer.endpoints.isEmpty &&
    writer.accepted.length == 2 &&
    ((writer.accepted.flatMap rootReceipts).map receiptId == [⟨2⟩, ⟨3⟩, ⟨0⟩, ⟨1⟩]) &&
    (bytes.extract 0 16).data == #[3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0] &&
    (bytes.extract 16 32).data == #[1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0] &&
    result.config.host.transcript == [accept 0 32, .returned 0 1,
      give 1 "bad-memory" 1 0, .refused 1 .badLoweringMemory,
      give 2 "bad-realloc" 1 0, .refused 2 .badLoweringRealloc,
      give 3 "give-record" 1 0, .returned 3 0,
      give 4 "give-record" 1 0, .refused 4 spent,
      accept 5 0, .returned 5 2,
      give 6 "give-record" 1 0, .refused 6 spent,
      give 7 "give-record" 2 16, .returned 7 0] &&
    result.config.host.refusals == [spent, spent, .badLoweringRealloc, .badLoweringMemory]

#guard regression

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.RecordExamples
