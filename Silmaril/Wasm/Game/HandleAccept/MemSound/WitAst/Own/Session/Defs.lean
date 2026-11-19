module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session

open Silmaril.Formats Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Execution.Core

/-- The owning table is a separate part of the host state. A writer callback receives
resolved nodes, not guest table indices, and cannot overwrite this table. -/
structure State (Q : Type) where
  resources : RT
  writer : Q

/-- A checked node import identified by its Core host code. The writer can answer a
well-formed node with an i32, or decline it by trapping. Other imports in this contract
do not allocate or free resource slots. -/
structure Contract (S : WitSig) (Q : Type) where
  code : Nat
  name : String × String
  tagOf : BitVec 32 → Option S.Tag
  mode : NodeMode
  node : Q → Op S → List (BitVec 32) → UCall Nat → UReply → Q → Prop
  other : Q → UCall Nat → UReply → Q → Prop

variable {S : WitSig} {Q : Type}

/-- The diagnostic is computed using the state at this host call. The memory address is
resolved by the instance, not by an unchecked default when the memory is absent. -/
def Contract.attempt (K : Contract S Q) (memory : Option Nat) (rt : RT) (call : UCall Nat) :
    Except NodeIssue ((Op S × List (BitVec 32)) × RT) :=
  match memory with
  | some addr => checkedAt K.mode K.name addr call (Nested.checkedNode S K.tagOf K.mode rt)
  | none => do
    checkNodeMode K.mode
    throw .missingMemory

/-- Checked rejection is an actual Core answer, not a missing writer event. A successful
node reply commits the newly reserved slots once. Other imports, and a writer choosing
to trap on a well-formed node, cannot modify the owning table. -/
inductive Answer (K : Contract S Q) (memory : Option Nat) :
    State Q → UCall Nat → UReply → State Q → Prop where
  | reject {state : State Q} {call : UCall Nat} {issue : NodeIssue} :
      call.target = K.code → K.attempt memory state.resources call = .error issue →
      Answer K memory state call ⟨call.store, .trap⟩ state
  | decline {state : State Q} {call : UCall Nat} {op : Op S} {children : List (BitVec 32)}
      {updated : RT} :
      call.target = K.code → K.attempt memory state.resources call = .ok ((op, children), updated) →
      K.node state.writer op children call ⟨call.store, .trap⟩ state.writer →
      Answer K memory state call ⟨call.store, .trap⟩ state
  | returnHandle {state : State Q} {call : UCall Nat} {op : Op S} {children : List (BitVec 32)}
      {updated : RT} {handle : BitVec 32} {store : Store Nat} {writer : Q} :
      call.target = K.code → K.attempt memory state.resources call = .ok ((op, children), updated) →
      KeepsCode call.store store → K.node state.writer op children call ⟨store, .values [.i32 handle]⟩ writer →
      Answer K memory state call ⟨store, .values [.i32 handle]⟩ ⟨updated, writer⟩
  | other {state : State Q} {call : UCall Nat} {reply : UReply} {writer : Q} :
      call.target ≠ K.code → K.other state.writer call reply writer →
      Answer K memory state call reply ⟨state.resources, writer⟩

/-- A stateful Core host. The traced session keeps this state across all exports, even
when a node import traps. No extra divergence rule hides a rejected import. -/
def Contract.env (K : Contract S Q) (memory : Option Nat) : SEnv UImp :=
  ⟨State Q, Answer K memory, fun _ _ => False⟩

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session
