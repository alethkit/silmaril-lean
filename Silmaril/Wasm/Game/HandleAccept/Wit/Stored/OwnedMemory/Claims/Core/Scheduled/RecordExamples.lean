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
@[expose] public def element : Option (WIT.ClosedType RtId) :=
  some (.record [("word", .prim .u16), ("resource", .own resource)])
@[expose] public def signature : Signature := ⟨Bool, (fun isTuple =>
  let owners : WIT.ClosedType RtId := .fixedList (.own resource) 2
  let reader : WIT.ClosedType RtId := .option (.stream element)
  if isTuple then .tuple [owners, reader] else .record [("owners", owners), ("reader", reader)]), fun _ => .fixed 0⟩
private def contract : Endpoints.Core.Contract signature :=
  ⟨0, ("host", "accept-node"), (fun tag => if tag == 0 then some false else if tag == 1 then some true else none),
    {}, ⟨0⟩⟩

private def wordFn (params results : Nat) : V1.FuncType :=
  ⟨List.replicate params (.int .i32), List.replicate results (.int .i32)⟩

private def coreMemory : engine.MemAddr := (0 : Nat)
private def readerMemory : engine.MemAddr := (1 : Nat)

private def imports : List (String × V1.FuncType × CanonHost engine) :=
  let accept := Endpoints.Core.Scheduled.acceptType contract
  let flat : V1.FuncType := ⟨[.int .i32], .int .i32 :: ABI.flatten .i32 (signature.payload true)⟩
  let recordFlat : V1.FuncType := ⟨[.int .i32], .int .i32 :: ABI.flatten .i32 (signature.payload false)⟩
  let flatIn := wordFn 6 2
  let wideIn : V1.FuncType := ⟨.int .i64 :: .int .i64 :: ABI.flatten .i64 (signature.payload true), flatIn.results⟩
  let asyncOpts : CanonOpts engine := { memory := some coreMemory, async_ := true }
  [("accept-node", accept, .embedder "accept-node" accept),
    ("give-record", wordFn 2 2, .embedder "give-record" (wordFn 2 2)),
    ("give-payload", wordFn 2 2, .embedder "give-payload" (wordFn 2 2)),
    ("bad-memory", wordFn 2 2, .embedder "bad-memory" (wordFn 2 2)),
    ("bad-realloc", wordFn 2 2, .embedder "bad-realloc" (wordFn 2 2)),
    ("new-own", wordFn 1 1, .builtin (.resourceNew resource .i32) ⟨0⟩),
    ("new-stream", ⟨[], [.int .i64]⟩, .builtin (.streamNew element) ⟨0⟩),
    ("rep", wordFn 1 1, .builtin (.resourceRep resource .i32) ⟨0⟩),
    ("close-reader", wordFn 1 0, .builtin (.streamDropReadable element) ⟨0⟩),
    ("close-writer", wordFn 1 0, .builtin (.streamDropWritable element) ⟨0⟩),
    ("give-flat", flat, .embedder "give-flat" flat),
    ("wrong-flat-schema", recordFlat, .embedder "wrong-flat-schema" recordFlat),
    ("accept-flat", flatIn, .embedder "accept-flat" flatIn),
    ("wide-flat", wideIn, .embedder "wide-flat" wideIn),
    ("write", wordFn 3 1, .builtin (.streamWrite element asyncOpts) ⟨0⟩)]

private def readerImports : List (String × V1.FuncType × CanonHost engine) :=
  let flat : V1.FuncType := ⟨[.int .i32], .int .i32 :: ABI.flatten .i32 (signature.payload true)⟩
  let asyncOpts : CanonOpts engine := { memory := some readerMemory, async_ := true }
  [("give-flat", flat, .embedder "give-flat" flat),
    ("read", wordFn 3 1, .builtin (.streamRead element asyncOpts) ⟨1⟩),
    ("cancel-read", wordFn 1 1, .builtin (.streamCancelRead element true) ⟨1⟩),
    ("new-set", wordFn 0 1, .builtin .waitableSetNew ⟨1⟩),
    ("join", wordFn 2 0, .builtin .waitableJoin ⟨1⟩),
    ("poll", wordFn 2 1, .builtin (.waitableSetPoll readerMemory) ⟨1⟩),
    ("close-set", wordFn 1 0, .builtin .waitableSetDrop ⟨1⟩),
    ("rep", wordFn 1 1, .builtin (.resourceRep resource .i32) ⟨1⟩),
    ("drop-own", wordFn 1 0, .builtin (.resourceDrop resource) ⟨1⟩),
    ("close-reader", wordFn 1 0, .builtin (.streamDropReadable element) ⟨1⟩)]

private def indexOf {kind : IndexKind} (index : Nat) : Idx kind := ⟨Fin.ofNat _ index⟩
private def word (value : Nat) : Instr := .intConst .i32 (BitVec.ofNat 32 value)
private def storeWord (ptr value : Nat) : List Instr :=
  [word ptr, word value, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩]

private def instantiateWith (initial : Store (CanonHost engine))
    (entries : List (String × V1.FuncType × CanonHost engine))
    (setup : String → List Instr) : Option (Store (CanonHost engine) × ModuleInst) := do
  let (store, addrs) := entries.foldl (fun (store, addresses) (_, type, code) =>
    let (next, addr) := SingleThreaded.allocHost store type code
    (next, addresses ++ [ExternAddr.func addr])) (initial, [])
  let names := entries.map (·.1)
  let wrapper := fun index =>
    let params := (entries[index]?.map (·.2.1.params.length)).getD 0
    let instructions := (names[index]?.map setup).getD []
    (⟨indexOf index, [], instructions ++ (List.range params).map (fun param => .localGet (indexOf param)) ++
      [.call (indexOf index)]⟩ : Func)
  let module_ : Module := {
    types := entries.map (·.2.1.toCoreRec)
    imports := names.zipIdx |>.map fun (name, index) => ⟨"host", name, .func (indexOf index)⟩
    memories := [⟨.i32, ⟨1, none⟩⟩]
    funcs := (List.range names.length).map wrapper
    exports := names.zipIdx |>.map fun (name, index) => ⟨name, .func (indexOf (index + names.length))⟩ }
  let (store, inst, none) ← Core3.prepareE? store module_ addrs | none
  return (store, inst)

private def instantiate : Option (Store (CanonHost engine) × ModuleInst) := do
  let (store, inst) ← instantiateWith {} imports fun name => match name with
    | "accept-node" => storeWord 32 1 ++ storeWord 36 2 ++ storeWord 40 1 ++ storeWord 44 3
    | "write" => storeWord 64 257 ++ storeWord 68 3
    | _ => []
  guard (inst.mems == [(0 : Nat)])
  return (store, inst)

private def exportAddr (inst : ModuleInst) (name : String) : Option engine.FuncAddr := do
  let (_, .func address) ← (Core3.instExports inst).find? (·.1 == name) | none
  return address

private def session (inst : ModuleInst) (useTuple : Bool) : Session grow signature (Ret engine) := do
  let run (name : String) (args : List Nat) (expected : List FlatValue) := do
    let some addr := exportAddr inst name | internal s!"missing Core export {name}"
    trapIf ((← callCore addr (args.map i32Flat)) != expected) (.internal s!"unexpected result: {name}")
  let refused := [i32Flat 1, i32Flat 0]
  let success (value : Nat) := [i32Flat 0, i32Flat value]
  let tag := if useTuple then 1 else 0
  let give := if useTuple then "give-payload" else "give-record"
  run "new-own" [77] [i32Flat 1]
  run "new-own" [77] [i32Flat 2]
  run "new-stream" [] [.int .i64 (BitVec.ofNat 64 (packEnds 3 4))]
  run "accept-node" [tag, 32, 0, 0] (success 1)
  run "bad-memory" [1, 0] refused
  run "bad-realloc" [1, 0] refused
  run give [1, 0] (success 0)
  run give [1, 0] refused
  run "rep" [3] [i32Flat 77]
  run "rep" [2] [i32Flat 77]
  run "accept-node" [tag, 0, 0, 0] (success 2)
  run give [1, 0] refused
  run give [2, 16] (success 0)
  run "close-reader" [3] []
  run "close-writer" [4] []
  return .unit

private def ready : HostReady (HostState signature) := fun _ _ => false

private def setup (useTuple : Bool) : Option (List (Binding signature) × Machine.Config engine (HostState signature)) := do
  let (store, inst) ← instantiate
  let .ok lower := Binding.giveRecord "give-record" ⟨0⟩ inst 0 .i32 .utf8 | none
  let .ok lowerPayload := Binding.givePayload "give-payload" ⟨0⟩ inst 0 .i32 .utf8 | none
  let badRealloc : Except Issue (Binding signature) :=
    if useTuple then Binding.givePayload "bad-realloc" ⟨0⟩ inst 0 .i32 .utf8 (some 0)
    else Binding.giveRecord "bad-realloc" ⟨0⟩ inst 0 .i32 .utf8 (some 0)
  let .ok badRealloc := badRealloc | none
  let badMemory : RecordDestination := ⟨99, .i32, none, .utf8⟩
  let bindings := [Binding.accept contract inst 0, lower, lowerPayload, badRealloc,
    ⟨"bad-memory", ⟨0⟩, if useTuple then .givePayload badMemory else .giveRecord badMemory⟩]
  let reference : CStore engine := { CStore.empty with
    core := store, insts := [{}], resourceTypes := [{ impl := some ⟨0⟩ }],
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }],
    threads := [{ status := .running, task := ⟨0⟩ }] }
  return (bindings, {
    store := reference, host := {}, conts := [none]
    ctl := [Machine.Activation.ofProg (some ⟨0⟩) (session inst useTuple)] })

private def run (bindings : List (Binding signature)) (config : Machine.Config engine (HostState signature)) :=
  Machine.run ready (specDispatch ready (host bindings)) (core3Exec grow) Machine.Oracle.first 1500 config

private theorem run_sound (bindings : List (Binding signature)) (config : Machine.Config engine (HostState signature)) :
    Machine.Steps .deterministic ready (specDispatch ready (host bindings)) config
      (run bindings config).labels (run bindings config).config :=
  Machine.run_sound ready (specDispatch ready (host bindings)) (core3Exec grow) Machine.Oracle.first 1500 config

private def regression (useTuple : Bool) : Bool :=
  match setup useTuple with
  | none => false
  | some (bindings, config) =>
    let result := run bindings config
    let writer := result.config.host.writer
    let bytes := (result.config.store.core.mems[0]?.map (·.bytes)).getD ByteArray.empty
    let spent := if useTuple then Issue.lowerPayload (.claims .unclaimed) else .lowerRecord (.claims .unclaimed)
    let tag := if useTuple then 1 else 0
    let name := if useTuple then "give-payload" else "give-record"
    let accept := fun ticket ptr => Event.entered ticket "accept-node"
      (Endpoints.Core.Scheduled.acceptType contract) [i32Flat tag, i32Flat ptr, i32Flat 0, i32Flat 0]
    let give := fun ticket name handle ptr => Event.entered ticket name (wordFn 2 2) [i32Flat handle, i32Flat ptr]
    result.outcome == .resolved && writer.held.isEmpty && writer.endpoints.isEmpty &&
    writer.accepted.length == 2 &&
    ((writer.accepted.flatMap rootReceipts).map receiptId == [⟨2⟩, ⟨3⟩, ⟨0⟩, ⟨1⟩]) &&
    (bytes.extract 0 16).data == #[3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0] &&
    (bytes.extract 16 32).data == #[1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0] &&
    result.config.host.transcript == [accept 0 32, .returned 0 1,
      give 1 "bad-memory" 1 0, .refused 1 .badLoweringMemory,
      give 2 "bad-realloc" 1 0, .refused 2 .badLoweringRealloc,
      give 3 name 1 0, .returned 3 0,
      give 4 name 1 0, .refused 4 spent,
      accept 5 0, .returned 5 2,
      give 6 name 1 0, .refused 6 spent,
      give 7 name 2 16, .returned 7 0] &&
    result.config.host.refusals == [spent, spent, .badLoweringRealloc, .badLoweringMemory]

#guard regression false
#guard regression true

private def flatSession (inst : ModuleInst) : Session grow signature (Ret engine) := do
  let run (name : String) (args : List Nat) (expected : List FlatValue) := do
    let some addr := exportAddr inst name | internal s!"missing Core export {name}"
    trapIf ((← callCore addr (args.map i32Flat)) != expected) (.internal s!"unexpected result: {name}")
  run "new-own" [77] [i32Flat 1]
  run "new-own" [77] [i32Flat 2]
  run "new-stream" [] [.int .i64 (BitVec.ofNat 64 (packEnds 3 4))]
  run "accept-node" [1, 32, 0, 0] ([0, 1].map i32Flat)
  run "wrong-flat-schema" [1] ([1, 0, 0, 0, 0].map i32Flat)
  run "give-flat" [1] ([0, 3, 2, 1, 1].map i32Flat)
  run "give-flat" [1] ([1, 0, 0, 0, 0].map i32Flat)
  run "rep" [3] [i32Flat 77]
  run "rep" [2] [i32Flat 77]
  run "close-reader" [1] []
  run "close-writer" [4] []
  return .unit

private def flatSetup : Option (List (Binding signature) × Machine.Config engine (HostState signature)) := do
  let (store, inst) ← instantiate
  let .ok flat := Binding.giveFlat "give-flat" ⟨0⟩ inst 0 .i32 .utf8 (signature.payload true) | none
  let .ok wrong := Binding.giveFlat "wrong-flat-schema" ⟨0⟩ inst 0 .i32 .utf8 (signature.payload false) | none
  let (_, initial) ← setup true
  let reference := { initial.store with core := store }
  return ([Binding.accept contract inst 0, flat, wrong],
    { initial with store := reference, ctl := [Machine.Activation.ofProg (some ⟨0⟩) (flatSession inst)] })

private def flatRegression : Bool :=
  match flatSetup with
  | none => false
  | some (bindings, config) =>
    let result := run bindings config
    let writer := result.config.host.writer
    let enter := fun ticket name type args => Event.entered ticket name type (args.map i32Flat)
    let flat : V1.FuncType := ⟨[.int .i32], .int .i32 :: ABI.flatten .i32 (signature.payload true)⟩
    let spent := Issue.lowerPayload (.claims .unclaimed)
    result.outcome == .resolved && writer.accepted.length == 1 &&
    writer.held.isEmpty && writer.endpoints.isEmpty &&
    result.config.host.transcript == [enter 0 "accept-node" (Endpoints.Core.Scheduled.acceptType contract) [1, 32, 0, 0],
      .returned 0 1, enter 1 "wrong-flat-schema" flat [1], .refused 1 .wrongPayloadType,
      enter 2 "give-flat" flat [1], .returnedFlat 2 ([3, 2, 1, 1].map i32Flat),
      enter 3 "give-flat" flat [1], .refused 3 spent]

#guard flatRegression

#guard (flatCompletion 0 [.int .i64, .float .f32] (.error .badSelection)).2 ==
  [i32Flat 1, .int .i64 0, .float .f32 0]

#guard (flatCompletion 0 [.int .i64, .float .f32] (.ok [i32Flat 3, .float .f32 7])).1 ==
  .refused 0 .wrongResultType

private def flatInputSession (inst : ModuleInst) : Session grow signature (Ret engine) := do
  let run (name : String) (args expected : List FlatValue) := do
    let some addr := exportAddr inst name | internal s!"missing Core export {name}"
    trapIf ((← callCore addr args) != expected) (.internal s!"unexpected result: {name}")
  let refused := [i32Flat 1, i32Flat 0]
  let inputs := [1, 2, 1, 3].map i32Flat
  run "new-own" [i32Flat 77] [i32Flat 1]
  run "new-own" [i32Flat 77] [i32Flat 2]
  run "new-stream" [] [.int .i64 (BitVec.ofNat 64 (packEnds 3 4))]
  run "wide-flat" (.int .i64 0 :: .int .i64 0 :: inputs) refused
  run "accept-flat" (i32Flat 0 :: i32Flat 1 :: inputs) refused
  run "accept-flat" (i32Flat 0 :: i32Flat 0 :: inputs) [i32Flat 0, i32Flat 1]
  run "give-flat" [i32Flat 1] ([0, 3, 2, 1, 1].map i32Flat)
  run "rep" [i32Flat 3] [i32Flat 77]
  run "rep" [i32Flat 2] [i32Flat 77]
  run "close-reader" [i32Flat 1] []
  run "close-writer" [i32Flat 4] []
  return .unit

private def flatInputSetup (program : ModuleInst → Session grow signature (Ret engine)) :
    Option (List (Binding signature) × Machine.Config engine (HostState signature)) := do
  let (store, inst) ← instantiate
  let .ok input := Binding.acceptFlat ("host", "accept-flat") ⟨0⟩ inst 0 { passing := .flat } true | none
  let .ok wide := Binding.acceptFlat ("host", "wide-flat") ⟨0⟩ inst 0 { address := .i64, passing := .flat } true | none
  let .ok output := Binding.giveFlat "give-flat" ⟨0⟩ inst 0 .i32 .utf8 (signature.payload true) | none
  let (_, initial) ← setup true
  let reference := { initial.store with core := store }
  return ([input, wide, output],
    { initial with store := reference, ctl := [Machine.Activation.ofProg (some ⟨0⟩) (program inst)] })

private def flatInputRegression : Bool :=
  match flatInputSetup flatInputSession with
  | some (bindings, config) =>
    let result := run bindings config
    let writer := result.config.host.writer
    let width := Issue.accept (.boundary (.boundary (.addressWidth .i32)))
    let arity := Issue.accept (.boundary (.boundary .badArity))
    let args := [1, 2, 1, 3].map i32Flat
    let input := wordFn 6 2
    let wide : V1.FuncType := ⟨.int .i64 :: .int .i64 :: ABI.flatten .i64 (signature.payload true), input.results⟩
    let output : V1.FuncType := ⟨[.int .i32], .int .i32 :: ABI.flatten .i32 (signature.payload true)⟩
    result.outcome == .resolved && writer.accepted.length == 1 && writer.held.isEmpty &&
    writer.endpoints.isEmpty && result.config.host.refusals == [arity, width] &&
    result.config.host.transcript == [
      .entered 0 "wide-flat" wide (.int .i64 0 :: .int .i64 0 :: args), .refused 0 width,
      .entered 1 "accept-flat" input (i32Flat 0 :: i32Flat 1 :: args), .refused 1 arity,
      .entered 2 "accept-flat" input (i32Flat 0 :: i32Flat 0 :: args), .returned 2 1,
      .entered 3 "give-flat" output [i32Flat 1], .returnedFlat 3 ([3, 2, 1, 1].map i32Flat)]
  | none => false

#guard flatInputRegression

private def expect (inst : ModuleInst) (name : String) (args : List Nat) (expected : List FlatValue) :
    Session grow signature Unit := do
  let some addr := exportAddr inst name | internal s!"missing Core export {name}"
  let result ← callCore addr (args.map i32Flat)
  trapIf (result != expected) (.internal s!"unexpected result: {name} {args} got {repr result}")

private def flatStreamWriter (inst : ModuleInst) : Session grow signature (Ret engine) := do
  let run := expect inst
  run "new-own" [77] [i32Flat 1]
  run "new-own" [77] [i32Flat 2]
  run "new-stream" [] [.int .i64 (BitVec.ofNat 64 (packEnds 3 4))]
  run "accept-flat" [0, 0, 1, 2, 1, 3] ([0, 1].map i32Flat)
  run "new-own" [97] [i32Flat 3]
  block (some ⟨1⟩)
  run "write" [4, 64, 1] [i32Flat (packStreamCopyResult .completed 1)]
  resumeThread ⟨1⟩
  run "close-writer" [4] []
  resumeThread ⟨1⟩
  return .unit

private def flatStreamReader (inst : ModuleInst) (stale : Bool) : Session grow signature (Ret engine) := do
  let run := expect inst
  let complete := packStreamCopyResult .completed 1
  let cx : LiftLowerContext engine := { inst := ⟨1⟩, opts := { memory := some readerMemory } }
  run "give-flat" [1] ([0, 1, 2, 1, 3].map i32Flat)
  run "new-set" [] [i32Flat 4]
  run "join" [3, 4] []
  run "read" [3, 80, 1] [i32Flat blocked]
  run "poll" [4, 96] [i32Flat EventCode.none.toNat]
  run "cancel-read" [3] [i32Flat (packStreamCopyResult .cancelled 0)]
  trapIf ((← readMem cx 80 8).data != #[0, 0, 0, 0, 0, 0, 0, 0]) (.internal "cancel wrote memory")
  run "read" [3, 80, 1] [i32Flat blocked]
  block (some ⟨0⟩)
  run "poll" [4, 96] [i32Flat EventCode.streamRead.toNat]
  trapIf ((← readMem cx 96 8).data != (u32Bytes 3).data ++ (u32Bytes complete).data)
    (.internal "unexpected stream readiness record")
  run "rep" [5] [i32Flat 97]
  run "rep" [1] [i32Flat 77]
  run "rep" [2] [i32Flat 77]
  run "drop-own" [5] []
  run "drop-own" [1] []
  run "drop-own" [2] []
  block none
  run "read" [3, 80, 1] [i32Flat (packStreamCopyResult .dropped 0)]
  run "join" [3, 0] []
  run "close-reader" [3] []
  run "close-set" [4] []
  if stale then run "read" [3, 80, 1] []
  return .unit

private def flatStreamSetup (stale : Bool) : Option (List (Binding signature) × Machine.Config engine (HostState signature)) := do
  let (store, writer) ← instantiate
  let (store, reader) ← instantiateWith store readerImports (fun _ => [])
  guard (reader.mems == [(1 : Nat)])
  let .ok input := Binding.acceptFlat ("host", "accept-flat") ⟨0⟩ writer 0 { passing := .flat } true | none
  let .ok output := Binding.giveFlat "give-flat" ⟨1⟩ reader 0 .i32 .utf8 (signature.payload true) | none
  let reference : CStore engine := { CStore.empty with
    core := store, insts := [{}, {}], resourceTypes := [{ impl := some ⟨0⟩ }],
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ },
      { ft := ⟨[], none, false⟩, opts := {}, inst := ⟨1⟩, caller := ⟨1⟩ }],
    threads := [{ status := .running, task := ⟨0⟩ }, { status := .blocked, task := ⟨1⟩ }] }
  let config : Machine.Config engine (HostState signature) := {
    store := reference
    host := {}
    conts := [none, some (Machine.Activation.ofProg (some ⟨1⟩) (flatStreamReader reader stale))],
    ctl := [Machine.Activation.ofProg (some ⟨0⟩) (flatStreamWriter writer)] }
  return ([input, output], config)

private def flatStreamRegression (stale : Bool) : Bool :=
  match flatStreamSetup stale with
  | some (bindings, config) =>
    let result := run bindings config
    let writer := result.config.host.writer
    let traps := result.labels.filterMap fun | .trap reason => some reason | _ => none
    result.outcome == (if stale then .trap else .resolved) &&
    traps == (if stale then [.unknownHandle 3] else []) &&
    writer.accepted.length == 1 && writer.held.isEmpty && writer.endpoints.isEmpty &&
    result.config.host.refusals.isEmpty &&
    (result.config.store.core.mems[1]?.map fun mem => (mem.bytes.extract 80 88).data) ==
      some #[1, 1, 0, 0, 5, 0, 0, 0] &&
    result.config.store.insts.map (fun inst => [1, 2, 3, 4, 5].map inst.handles.get?) ==
      [[none, none, none, none, none], [none, none, none, none, none]]
  | none => false

#guard flatStreamRegression false
#guard flatStreamRegression true

private def flatBindingIssue {sig : Signature} (result : Except Issue (Binding sig)) : Option Issue :=
  match result with
  | .ok _ => none
  | .error issue => some issue

private def inactiveBorrow : Signature :=
  ⟨Unit, fun _ => .list (.option (.borrow resource)), fun _ => .fixed 0⟩

#guard flatBindingIssue (Binding.acceptFlat (sig := inactiveBorrow) ("host", "bad") ⟨0⟩ {} 0
  { passing := .flat } ()) ==
  some (.accept (.claims (.lift (.schema .storedBorrow))))

#guard flatBindingIssue (Binding.acceptFlat (sig := signature) ("host", "bad") ⟨0⟩ {} 0
  { passing := .flat, asynchronous := true } true) == some (.accept (.boundary (.boundary .asyncCall)))

#guard flatBindingIssue (Binding.acceptFlat (sig := signature) ("host", "bad") ⟨0⟩ {} 0 {} true) ==
  some .wrongPassingMode

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.RecordExamples
