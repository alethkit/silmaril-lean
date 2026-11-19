module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.HostWrite.Defs
import Silmaril.Wasm.Component.Reference.HostWrite.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}
  {prof : ProfileKind} {ready : HostReady (HostState sig)}
  {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

/-- Record the import's typed arguments and reserve a fresh ticket before routing it. The
same ticket stays in the continuation even if a destructor later reenters this dispatcher. -/
theorem enter_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (bindings : List (Binding sig))
    (name : String) (type : V1.FuncType) (args : List FlatValue)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> dispatchImport bindings name type args), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.enter name type args
        ctl := ⟨thread, .prog (.flat <$> route config.host.nextTicket bindings name type args), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.enter_steps
    config thread segments rest bindings name type args pending

/-- In any activation, recording a completion returns exactly the corresponding Core status
pair without changing the writer, component store or suspended work. -/
theorem finish_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig)))
    (ticket : Nat) (result : Except Issue Nat)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> finish ticket result), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.record (completion ticket result).1
        ctl := ⟨thread, .prog (.pure (.flat (completion ticket result).2)), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.finish_steps
    config thread segments rest ticket result pending

/-- Journal a complete flat payload and its status, including shape-correct padding on refusal. -/
theorem finish_flat_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat) (shape : List NumType)
    (result : Except Issue (List FlatValue))
    (pending : config.ctl = ⟨thread, .prog (.flat <$> writeCompletion (flatCompletion ticket shape result)),
      segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.record (flatCompletion ticket shape result).1
        ctl := ⟨thread, .prog (.pure (.flat (flatCompletion ticket shape result).2)), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.write_completion_steps
    config thread segments rest _ pending

theorem flatCompletion_type (ticket : Nat) (shape : List NumType) (result : Except Issue (List FlatValue)) :
    (flatCompletion ticket shape result).2.map Stored.flatType = .int .i32 :: shape :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.flatCompletion_type
    ticket shape result

/-- A linking error records the typed diagnostic before the real reference trap, not a
status return. A destructor trap follows its own path and never calls this handler. -/
theorem binding_trap_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat) (issue : Issue)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> rejectBinding ticket issue), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .trap (.hostTrap "invalid mixed acceptor import binding")]
      (StepDefs.trapCfg { config with host := config.host.record (.bindingTrap ticket issue) }) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.binding_trap_steps
    config thread segments rest ticket issue pending

/-- The diagnostic history is append-only even for host-injected programs whose writes
need not follow the stronger writer policy. -/
theorem extends_of_steps (bindings : List (Binding sig))
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) initial labels final)
    (safe : CfgSafe Extends initial) (runSafe : RunSafe Extends labels) : Extends initial.host final.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.extends_of_steps
    bindings steps safe runSafe

/-- For arbitrary machine prefixes, including trapping or suspended calls, diagnostic history
only grows and every writer change follows the publication and spend policy. Host-supplied
raw programs must respect the same write policy. -/
theorem checked_of_steps (bindings : List (Binding sig))
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels) :
    Extends initial.host final.host ∧ WriterRun initial.host.writer final.host.writer :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.checked_of_steps
    bindings steps safe runSafe

/-- An initialized session admits arbitrary ordinary host events and internal scheduling
without any hypothesis about the component or its export sequence. -/
theorem checked_of_session (bindings : List (Binding sig)) (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels) :
    Extends state final.host ∧ WriterRun state.writer final.host.writer :=
  checked_of_steps bindings steps (Component.Reference.HostWrite.cfgSafe_init _ _)
    (fun program member => (ordinary program member).elim)

theorem extends_of_session (bindings : List (Binding sig)) (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels) : Extends state final.host :=
  (checked_of_session bindings store state steps ordinary).1

/-- Once spent, an owner that was observed in an accepted root cannot be reacquired as the
same arena identity, even if a later Core call reuses the guest slot or representation. -/
theorem WriterRun.owner_retired {before after : State sig} {id : HandleObjId}
    (run : WriterRun before after) (retired : before.retiredOwner id) : after.retiredOwner id :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.owner_retired run retired

/-- Readable endpoint identity can be acquired again, but only through a new root
publication. Spending or a rejected call cannot restore an earlier claim. -/
theorem WriterRun.endpoint_publications {before after : State sig} (run : WriterRun before after) :
    ∃ roots, after.accepted = roots ++ before.accepted ∧
      ∀ id ∈ after.endpoints, id ∈ before.endpoints ∨ id ∈ roots.flatMap rootEndpoints :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.endpoint_publications run

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
