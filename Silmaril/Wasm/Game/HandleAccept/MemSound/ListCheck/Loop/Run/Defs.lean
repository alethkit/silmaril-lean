module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Replies.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Formats.Api
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom utf8?)
open Silmaril.Wasm.Game.HandleAccept.MemSound.Readers (symTextAns blobAns)

/-- The actual executable loop checker variants. -/
inductive Checker where
  | symbols
  | blobs

def Checker.imports : Checker → ListImports
  | .symbols => {}
  | .blobs => blobImports

def Checker.decodeChild : Checker → HostReply → BitVec 32 → SxA MemAtom (BitVec 32)
  | .symbols => symTextAns
  | .blobs => blobAns

/-- The semantic child denoted by the payload, before constructing a Core reply.
Malformed UTF-8 is not a symbol; all byte sequences are valid blobs. -/
def Checker.decodeBytes : Checker → List UInt8 → Option MemAtom
  | .symbols, bytes => (utf8? bytes).map fun text => ⟨.symbol, by decide, text⟩
  | .blobs, bytes => some ⟨.bytes, by decide, bytes⟩

/-- A host can supply a fixed logical vector and any child payloads, while rewriting bytes
on each answer. `ready` records what must survive each answer to keep the script available. -/
structure ReplyPlan (host : SEnv UImp) (ready : Store Nat → Prop)
    (ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32))
    (root : BitVec 32) (handles : List (BitVec 32))
    (answerFor : BitVec 32 → SxA MemAtom (BitVec 32)) : Prop where
  items : ∀ store state, ready store → ∃ next nextState mem,
    host.Ans state ⟨0, store, [.i32 root, .i32 0]⟩ ⟨next, .values []⟩ nextState ∧
    ready next ∧ next.funcs = store.funcs ∧ next.mems[0]? = some mem ∧
    itemsList mem.bytes 0 = some handles ∧ mem.bytes.size ≤ 2 ^ 32
  child : ∀ handle ∈ handles, ∀ store state, ready store → ∃ next nextState,
    host.Ans state ⟨1, store, [.i32 handle, .i32 0]⟩ ⟨next, .values []⟩ nextState ∧
    ready next ∧ next.funcs = store.funcs ∧
    ans ⟨.values [], memOf (some 0) next⟩ 0 = answerFor handle

/-- Observations in the remaining rounds, up to and including the acceptance call.
Every round freshly reads the whole vector, including the last round. -/
def remainingReads (root : BitVec 32) (handles remaining : List (BitVec 32))
    (answerFor : BitVec 32 → SxA MemAtom (BitVec 32)) : List MemREv :=
  remaining.flatMap (fun handle => [.read (.items root) (.items handles),
    .read (.atom handle) (answerFor handle)]) ++ [.read (.items root) (.items handles), .accept root]

/-- A one-memory store in which the script has `capacity` bytes to work with. -/
def ReplySpace (capacity : Nat) (store : Store Nat) : Prop :=
  ∃ mem, store.mems = [mem] ∧ mem.bytes.size = capacity

/-- Example reply semantics: use the checked encoder for `items`, and replace the bytes with
the supplied child payload for `child`. An encoder error cannot produce a successful reply. -/
inductive CompactReply (handles : List (BitVec 32)) (childBytes : BitVec 32 → ByteArray) :
    UCall Nat → UReply → Prop where
  | items {store : Store Nat} {mem : MemInst} {root : BitVec 32} {bytes : ByteArray} :
      store.mems = [mem] → writeItemsReply mem.bytes handles = .ok bytes →
      CompactReply handles childBytes ⟨0, store, [.i32 root, .i32 0]⟩
        ⟨store.setMem 0 { mem with bytes }, .values []⟩
  | child {store : Store Nat} {mem : MemInst} {handle : BitVec 32} :
      store.mems = [mem] → handle ∈ handles →
      CompactReply handles childBytes ⟨1, store, [.i32 handle, .i32 0]⟩
        ⟨store.setMem 0 { mem with bytes := childBytes handle }, .values []⟩
  | accept {store : Store Nat} {root : BitVec 32} :
      CompactReply handles childBytes ⟨2, store, [.i32 root]⟩ ⟨store, .values []⟩

def compactHost (handles : List (BitVec 32)) (childBytes : BitVec 32 → ByteArray) : SEnv UImp where
  S := Unit
  Ans _ call reply _ := CompactReply handles childBytes call reply
  Div _ _ := False

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
