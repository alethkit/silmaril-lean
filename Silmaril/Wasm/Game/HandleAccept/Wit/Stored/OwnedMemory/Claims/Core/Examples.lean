module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Thms
meta import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Defs
import Silmaril.Wasm.Game.HandleAccept.MemSound.Ast.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Examples

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)

public def resource : RtId := ⟨0⟩
public def element : Option (WIT.ClosedType RtId) := some (.prim .u16)

public inductive Tag where
  | mixed | invalid | lateTrap

@[expose] public def sig : Signature :=
  ⟨Tag, fun
    | .mixed => .record [("owner", .own resource), ("read", .stream element)]
    | .invalid => .result (some (.own resource)) (some (.list (.option (.borrow resource))))
    | .lateTrap => .tuple [.own resource, .stream element, .own resource], fun _ => .fixed 0⟩

private def contract : Contract sig :=
  ⟨0, ("wit", "accept-node"), fun raw => match raw.toNat with
    | 0 => some .mixed | 1 => some .invalid | 2 => some .lateTrap | _ => none, {}, ⟨0⟩⟩

private abbrev grow := SingleThreaded.neverFail
private abbrev engine := core3 grow

private def writeWord (address value : Nat) : List Instr :=
  [.intConst .i32 (BitVec.ofNat 32 address), .intConst .i32 (BitVec.ofNat 32 value),
    .intStore .i32 none ⟨0⟩ ⟨0, 0⟩]

private def body (tag first second : Nat) : List Instr :=
  writeWord 16 first ++ writeWord 20 second ++ writeWord 24 1 ++
    [.intConst .i32 (BitVec.ofNat 32 tag), .intConst .i32 16, .intConst .i32 0, .intConst .i32 0,
      .call ⟨0⟩]

private def module_ : Module where
  types := [HandleAccept.MemSound.Ast.tyTag, ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  imports := [⟨"wit", "accept-node", .func ⟨0⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨1⟩, [], body 1 0 1⟩, ⟨⟨1⟩, [], body 0 1 2⟩,
    ⟨⟨1⟩, [], body 2 4 5⟩, ⟨⟨1⟩, [], body 0 7 8⟩]
  exports := [⟨"unsupported", .func ⟨1⟩⟩, ⟨"first", .func ⟨2⟩⟩,
    ⟨"late-trap", .func ⟨3⟩⟩, ⟨"retry", .func ⟨4⟩⟩]

private def initialArena (E : CoreEngine) : CStore E :=
  let store : CStore E := { CStore.empty with
    resourceTypes := [{ impl := some ⟨0⟩ }],
    resHandles := List.replicate 3 { rt := resource, rep := 77, own := true } }
  let (reference, table) := ([0, 1, 2] : List Nat).foldl (fun (reference, table) index =>
    let (next, readable, writable) := newStream element (some ⟨0⟩) reference
    let entries := [HandleEntry.resource ⟨index⟩, .waitable (.end_ readable), .waitable (.end_ writable)]
    (HandleSt.setEndIndex writable (3 * index + 3) (HandleSt.setEndIndex readable (3 * index + 2) next),
      entries.foldl (fun inst entry => inst.addHandle entry) table)) (store, ({} : InstState))
  { reference with insts := [table] }

private def initial : World grow sig := ⟨initialArena engine, {}⟩

private def coreValue : FlatValue → Val
  | .int kind word => .num ⟨.int kind, word⟩
  | .float kind word => .num ⟨.float kind, word⟩

private def execute (memory : Nat) : Nat → Store Nat → SingleThreaded.Thread → World grow sig →
    List Issue → Except String (Store Nat × World grow sig × CallResult × List Issue)
  | 0, _, _, _, _ => .error "Core regression ran out of steps"
  | fuel + 1, store, thread, world, issues =>
    match engine.status store thread with
    | .returned result => .ok (store, world, result, issues.reverse)
    | .stuck => .error "Core instance stuck"
    | .running =>
      match (core3Exec grow).step? (store, thread) with
      | none => .error "Core interpreter could not step"
      | some (updated, next) => execute memory fuel updated next world issues
    | .callout target args =>
      let (updated, result) := attempt contract (some memory) world ⟨target, store, args.map coreValue⟩
      match result with
      | .error issue => execute memory fuel store (engine.resume store thread .trap) updated (issue :: issues)
      | .ok handle => execute memory fuel store
          (engine.resume store thread (.values [.int .i32 handle])) updated issues

private def replay : Except String Bool := do
  let (withHost, hostAddr) := SingleThreaded.allocHost ({} : Store Nat)
    ⟨List.replicate 4 (.int .i32), [.int .i32]⟩ 0
  let some (store, instanceInfo, none) := Core3.prepareE? withHost module_ [.func hostAddr]
    | throw "could not instantiate the Core acceptor"
  let some memory := instanceInfo.mems[0]? | throw "no linked memory"
  let invoke (name : String) (current : Store Nat) (world : World grow sig) := do
    let some (ExternAddr.func address) := ((Core3.instExports instanceInfo).find? (·.1 == name)).map (·.2)
      | throw "no exported Core function"
    execute memory 72 current (SingleThreaded.Thread.invokeFlat address []) world []
  let slot (state : World grow sig) (index : Nat) :=
    (state.reference.inst? ⟨0⟩).bind (fun inst => inst.handles.get? index)
  let (store, world, rejected, issues) ← invoke "unsupported" store initial
  let preflight := rejected == .trap && issues == [.boundary (.stored (.lift .storedBorrow))] &&
    world.writer.accepted.isEmpty && world.writer.held.isEmpty && world.writer.endpoints.isEmpty &&
    slot world 1 == some (.resource ⟨0⟩) && slot world 2 == some (.waitable (.end_ ⟨0⟩))
  let (store, world, accepted, acceptIssues) ← invoke "first" store world
  let (store, world, late, lateIssues) ← invoke "late-trap" store world
  let prior := late == .trap && lateIssues == [.localEffect (.trapped (.unknownHandle 1))] &&
    world.writer.accepted.length == 1 && world.writer.held.map receiptId == [⟨0⟩] &&
    world.writer.endpoints == [⟨0⟩] && (slot world 4).isNone && (slot world 5).isNone &&
    ((world.reference.end? ⟨2⟩).map (fun endpoint => (endpoint.owner, endpoint.index))) == some (none, none) &&
    (store.mems[memory]?.map fun mem => (mem.bytes.extract 16 24).data) == some #[4, 0, 0, 0, 5, 0, 0, 0]
  let (_, world, retry, retryIssues) ← invoke "retry" store world
  pure (preflight && accepted == .values [.int .i32 1] && acceptIssues.isEmpty && prior &&
    retry == .values [.int .i32 2] && retryIssues.isEmpty && world.writer.accepted.length == 2 &&
    world.writer.held.map receiptId == [⟨2⟩, ⟨0⟩] && world.writer.endpoints == [⟨4⟩, ⟨0⟩])

#guard replay == .ok true

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Examples
