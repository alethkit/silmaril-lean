module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract runLocal)
open Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst (NodeArgs)

inductive Issue where
  | boundary (issue : Endpoints.Core.Issue)
  | localEffect (issue : Endpoints.Core.LocalIssue)
  | claims (issue : Claims.Issue)
  deriving DecidableEq, Repr

structure World (grow : SingleThreaded.GrowOracle) (sig : Signature) where
  reference : CStore (core3 grow)
  writer : State sig := {}

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

def preflight (contract : Contract sig) (memory : Option Nat) (state : World grow sig)
    (call : UCall Nat) : Except Issue (NodeArgs sig.Tag × List (Tree sig)) := do
  if call.target != contract.code then throw (.boundary (.unexpectedImport call.target))
  (contract.preflightOperands OwnedMemory.checkSchema memory state.writer.accepted call).mapError .boundary

def load (contract : Contract sig) (memory : Option Nat) (state : World grow sig)
    (call : UCall Nat) : CStore (core3 grow) × Except Issue (Tree sig) :=
  match preflight contract memory state call with
  | .error issue => (state.reference, .error issue)
  | .ok (args, children) =>
    let cx : LiftLowerContext (core3 grow) :=
      { opts := { memory, encoding := contract.mode.encoding }, inst := contract.inst }
    let live := { state.reference with core := { mems := call.store.mems } }
    let (after, result) := runLocal
      (OwnedMemory.buildNode sig Component.Limits.spec Quirks.none cx args.tag (.memory args.payload) children) live
    ({ after with core := state.reference.core },
      (result.mapError .localEffect).bind fun lifted => lifted.mapError (Issue.claims ∘ Claims.Issue.lift))

/-- Receipt-aware atomic `accept-node`. A load trap preserves canonical table effects,
but no rejected call can publish a tree or either class of claim. -/
def attempt (contract : Contract sig) (memory : Option Nat) (state : World grow sig)
    (call : UCall Nat) : World grow sig × Except Issue (BitVec 32) :=
  let (reference, result) := load contract memory state call
  match result.bind (fun tree => (state.writer.register tree).mapError .claims) with
  | .error issue => ({ state with reference }, .error issue)
  | .ok writer => (⟨reference, writer⟩, .ok (BitVec.ofNat 32 writer.accepted.length))

/-- Keep the typed diagnostic at the host boundary. The synchronous Core import ABI
returns a handle or traps the current invocation; it does not undo the guest's writes. -/
def answer (contract : Contract sig) (memory : Option Nat) (state : World grow sig)
    (call : UCall Nat) (reply : UReply) (updated : World grow sig) : Prop :=
  let (next, result) := attempt contract memory state call
  updated = next ∧ reply = ⟨call.store, match result with
    | .ok handle => .values [.num ⟨.int .i32, handle⟩]
    | .error _ => .trap⟩

def env (contract : Contract sig) (grow : SingleThreaded.GrowOracle) (memory : Option Nat) : SEnv UImp :=
  ⟨World grow sig, answer contract memory, fun _ _ => False⟩

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
