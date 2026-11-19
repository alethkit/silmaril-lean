module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.HostWrite.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Thms
import Silmaril.Wasm.Component.Reference.HostWrite.Thms
import Silmaril.Wasm.Component.Reference.Canon.Builtins.Resource.Thms
import Silmaril.Wasm.Component.Reference.Canon.Lift.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordEffects

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element Channel.endKind Endpoint)

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}
  {prof : ProfileKind} {ready : HostReady (HostState sig)}
  {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

theorem enter_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (bindings : List (Binding sig))
    (name : String) (type : V1.FuncType) (args : List FlatValue)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> dispatchImport bindings name type args), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.enter name type args
        ctl := ⟨thread, .prog (.flat <$> route config.host.nextTicket bindings name type args), segments⟩ :: rest } :=
  .cons (.hostGet pending) (.cons (.hostSet rfl) (.refl _))

theorem finish_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig)))
    (ticket : Nat) (result : Except Issue Nat)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> finish ticket result), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.record (completion ticket result).1
        ctl := ⟨thread, .prog (.pure (.flat (completion ticket result).2)), segments⟩ :: rest } := by
  cases result <;> exact .cons (.hostGet pending) (.cons (.hostSet rfl) (.refl _))

theorem binding_trap_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat) (issue : Issue)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> rejectBinding ticket issue), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .trap (.hostTrap "invalid mixed acceptor import binding")]
      (StepDefs.trapCfg { config with host := config.host.record (.bindingTrap ticket issue) }) := by
  exact .cons (.hostGet pending) (.cons (.hostSet rfl) (.cons (.trap rfl) (.refl _)))

private abbrev Safe {Value : Type} (program : Session grow sig Value) := HostSafe CheckedWrite none program

private theorem readOnly {Value : Type} {program : Session grow sig Value}
    (safe : P.InvW (fun _ => True) (fun _ => False) program) : Safe program :=
  HostWrite.hostSafe_of_invW safe _

private theorem record_safe (state : HostState sig) (event : Event) : CheckedWrite state (state.record event) :=
  ⟨⟨by simp [HostState.transcript, HostState.record], le_rfl⟩, .same _⟩

private theorem spend_safe (update : Stored.OwnedMemory.Claims.Spend) :
    Safe ((claims (grow := grow) (sig := sig)).spend update) :=
  .get none fun _ => .set ⟨⟨List.prefix_rfl, le_rfl⟩, .spend _ _⟩ (.pure none ())

private theorem read_safe : Safe ((claims (grow := grow) (sig := sig)).read) :=
  .get none fun state => .pure _ state.writer

private theorem publish_safe (tree : Stored.OwnedMemory.Tree sig) :
    Safe (publishRoot (grow := grow) tree) := by
  refine .get none fun current => ?_
  change HostSafe CheckedWrite (some current) ((match current.writer.register tree with
    | .error issue => pure (.error (.accept (.claims issue)))
    | .ok writer => do
      hostSet { current with writer }
      return .ok ((BitVec.ofNat 32 writer.accepted.length).toNat)) : Session grow sig (Except Issue Nat))
  split
  · exact .pure (some current) _
  · exact .set ⟨⟨List.prefix_rfl, le_rfl⟩, .publish _ (by assumption)⟩ (.pure none _)

private theorem accept_safe (contract : Stored.Endpoints.Core.Contract sig) (memory : Option Nat)
    (args : List FlatValue) : Safe (accept (grow := grow) contract memory args) := by
  unfold accept
  refine HostWrite.bind (readOnly P.Inv.hostGet) fun state => ?_
  refine HostWrite.bind (readOnly P.Inv.getStore) fun reference => ?_
  refine HostWrite.bind (readOnly (P.Inv.modifyStore (fun _ _ => trivial))) fun _ => ?_
  split
  · exact .pure none _
  · exact publish_safe _

private theorem give_safe (cx : LiftLowerContext (core3 grow)) (resource : RtId) (id : HandleObjId) :
    Safe ((claims (sig := sig)).give Limits.spec cx resource id) := by
  unfold Stored.OwnedMemory.Claims.Access.give
  refine HostWrite.bind read_safe fun state => ?_
  split
  · exact .pure none _
  · refine HostWrite.bind (readOnly (P.Inv.lowerOwn (fun _ _ _ => trivial) (fun _ _ _ _ => trivial) _ _ _ _)) fun _ => ?_
    exact HostWrite.bind (spend_safe _) fun _ => .pure none _

private theorem giveEndpoint_safe (cx : LiftLowerContext (core3 grow)) (channel : Channel) (element : Element)
    (endpoint : Endpoint (channel.endKind .read) element) :
    Safe ((claims (sig := sig)).giveEndpoint Limits.spec cx channel element endpoint) := by
  unfold Stored.OwnedMemory.Claims.Access.giveEndpoint
  refine HostWrite.bind read_safe fun _ => ?_
  split
  · exact .pure none _
  · refine HostWrite.bind (readOnly P.Inv.getStore) fun _ => ?_
    split
    · exact .pure none _
    · refine HostWrite.bind (spend_safe _) fun _ => ?_
      refine HostWrite.bind (readOnly (P.Inv.lowerAsyncValue (fun _ _ _ _ => trivial)
        (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) _ _ _ _)) fun _ => .pure none _

private theorem drop_safe (resource : RtId) (id : HandleObjId) :
    Safe ((claims (grow := grow) (sig := sig)).drop (destructorCall Limits.spec Quirks.none) resource id) := by
  unfold Stored.OwnedMemory.Claims.Access.drop
  refine HostWrite.bind read_safe fun _ => ?_
  split
  · exact .pure none _
  · refine HostWrite.bind (readOnly Builtins.Inv.resourceEnter) fun inst => ?_
    refine HostWrite.bind (readOnly (P.Inv.dropHandleTail (by intros; trivial) _ _)) fun request => ?_
    cases request with
    | none => exact readOnly (P.Inv.internal _)
    | some request =>
      refine HostWrite.bind (spend_safe _) fun _ => ?_
      have hyps : LiftHyps (E := core3 grow) (fun _ => True) := by
        repeat' (first | (intro) | constructor)
      exact HostWrite.bind (readOnly (P.Inv.destructorCall hyps _ _ inst request)) fun _ => .pure none _

private theorem record_prepare_safe (cx : LiftLowerContext (core3 grow)) (plan : List Stored.Endpoints.RecordLower.Object) :
    Safe ((Stored.OwnedMemory.Claims.Record.authority (recordClaims (sig := sig)) Limits.spec cx).prepare plan) :=
  HostWrite.bind (readOnly P.Inv.getStore) fun _ => HostWrite.bind read_safe fun _ => .pure none _

private theorem record_transfer_safe (cx : LiftLowerContext (core3 grow)) (index : Nat)
    (object : Stored.Endpoints.RecordLower.Object) :
    Safe ((Stored.OwnedMemory.Claims.Record.authority (recordClaims (sig := sig)) Limits.spec cx).transfer index object) := by
  refine HostWrite.bind read_safe fun state => ?_
  cases object with
  | owner receipt =>
    dsimp only
    split
    · exact .pure none _
    · refine HostWrite.bind (readOnly (P.Inv.lowerOwn (fun _ _ _ => trivial) (fun _ _ _ _ => trivial)
        _ _ _ _)) fun _ => ?_
      exact HostWrite.bind (spend_safe _) fun _ => .pure none _
  | shared object =>
    cases object with
    | endpoint channel element id =>
      refine HostWrite.bind (readOnly P.Inv.getStore) fun _ => ?_
      split
      · exact .pure none _
      · refine HostWrite.bind (spend_safe _) fun _ => ?_
        exact HostWrite.bind (readOnly (P.Inv.lowerAsyncValue (fun _ _ _ _ => trivial)
          (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) _ _ _ _)) fun _ => .pure none _
    | errorContext id =>
      refine HostWrite.bind (readOnly P.Inv.getStore) fun _ => ?_
      split
      · exact .pure none _
      · exact HostWrite.bind (readOnly (P.Inv.lowerErrorContext (fun _ _ _ _ => trivial) _ _ _)) fun _ => .pure none _

private theorem lower_root_safe (cx : LiftLowerContext (core3 grow)) (tree : Stored.OwnedMemory.Tree sig)
    (output : Stored.Lower.Output) :
    Safe (Stored.OwnedMemory.Claims.Record.lowerRoot recordClaims Limits.spec Quirks.none cx tree output) := by
  cases tree with
  | atom impossible => exact impossible.elim
  | tag label children arity =>
    exact RecordEffects.compiled_safe _ _ _ _ _ _ _ _ (record_prepare_safe cx) (record_transfer_safe cx)

private theorem lower_payload_safe (cx : LiftLowerContext (core3 grow)) (tree : Stored.OwnedMemory.Tree sig)
    (output : Stored.Lower.Output) :
    Safe (Stored.OwnedMemory.Claims.Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none cx tree output) := by
  cases tree with
  | atom impossible => exact impossible.elim
  | tag label children arity =>
    exact RecordEffects.compiled_value_safe _ _ _ _ _ _ _ _ (record_prepare_safe cx) (record_transfer_safe cx)

private theorem give_memory_safe (inst : InstId) (destination : RecordDestination) (args : List FlatValue)
    (lower : LiftLowerContext (core3 grow) → Stored.OwnedMemory.Tree sig → Nat →
      Session grow sig (Except Stored.Endpoints.RecordLower.Issue Unit))
    (diagnose : Stored.Endpoints.RecordLower.Issue → Issue)
    (safe : ∀ cx tree ptr, Safe (lower cx tree ptr)) :
    Safe (giveToMemory inst destination args lower diagnose) := by
  unfold giveToMemory
  split
  · split
    · exact .pure none _
    · refine HostWrite.bind (readOnly P.Inv.getStore) fun _ => ?_
      split
      · exact .pure none _
      · refine HostWrite.bind (.get none fun _ => .pure _ _) fun selected => ?_
        cases selected with
        | none => exact .pure none _
        | some tree => exact HostWrite.bind (safe _ tree _) fun _ => .pure none _
  · exact .pure none _

private theorem withTree_safe (args : List FlatValue)
    (use : Stored.OwnedMemory.Tree sig → Nat → Session grow sig (Except Issue Nat))
    (safe : ∀ tree index, Safe (use tree index)) : Safe (withTree args use) := by
  unfold withTree
  split
  · refine HostWrite.bind (.get none fun _ => .pure _ _) fun selected => ?_
    cases selected with
    | none => exact .pure none _
    | some tree => exact safe tree _
  · exact .pure none _

private theorem invoke_safe (binding : Binding sig) (args : List FlatValue) :
    Safe (Stored.OwnedMemory.Claims.Core.Scheduled.invoke (grow := grow) binding args) := by
  unfold Stored.OwnedMemory.Claims.Core.Scheduled.invoke
  refine HostWrite.bind (readOnly P.Inv.currentInst?) fun current => ?_
  refine HostWrite.bind (readOnly P.Inv.getStore) fun store => ?_
  dsimp only
  split
  · exact .pure none _
  · cases binding.action <;> dsimp only
    case accept =>
      split
      · exact .pure none _
      · exact accept_safe _ _ _
    case giveOwner =>
      apply withTree_safe
      intro tree position
      split
      · exact HostWrite.bind (give_safe _ _ _) fun _ => .pure none _
      · exact .pure none _
    case dropOwner =>
      apply withTree_safe
      intro tree position
      split
      · exact HostWrite.bind (drop_safe _ _) fun _ => .pure none _
      · exact .pure none _
    case giveEndpoint =>
      apply withTree_safe
      intro tree position
      split
      · exact HostWrite.bind (giveEndpoint_safe _ _ _ _) fun _ => .pure none _
      · exact .pure none _
    case giveRecord => exact give_memory_safe _ _ _ _ _ fun cx tree ptr => lower_root_safe cx tree (.memory ptr)
    case givePayload => exact give_memory_safe _ _ _ _ _ fun cx tree ptr => lower_payload_safe cx tree (.memory ptr)

private theorem finish_safe (ticket : Nat) (result : Except Issue Nat) :
    Safe (finish (grow := grow) (sig := sig) ticket result) := by
  cases result <;> exact .get none fun state => .set (record_safe state _) (.pure none _)

private theorem binding_trap_safe (ticket : Nat) (issue : Issue) :
    Safe (rejectBinding (grow := grow) (sig := sig) ticket issue) :=
  .get none fun state => .set (record_safe state _) (readOnly (P.Inv.trap _))

private theorem route_safe (ticket : Nat) (bindings : List (Binding sig)) (name : String)
    (type : V1.FuncType) (args : List FlatValue) : Safe (route (grow := grow) ticket bindings name type args) := by
  unfold route
  split
  · exact binding_trap_safe _ _
  · split
    · exact binding_trap_safe _ _
    · exact HostWrite.bind (invoke_safe _ _) (finish_safe _)
  · exact binding_trap_safe _ _

private theorem host_safe (bindings : List (Binding sig)) :
    HostImplSafe CheckedWrite (host (grow := grow) bindings) := by
  constructor
  · intro name caller; exact readOnly (P.Inv.internal _)
  · intro name type args
    refine .get none fun state => .set ?_ (route_safe _ _ _ _ _)
    exact ⟨⟨by simp [HostState.enter, HostState.transcript], Nat.le_succ _⟩, .same _⟩
  · intro name thread; exact readOnly (P.Inv.internal _)
  · intro buffer; exact readOnly (P.Inv.internal _)
  · intro cancel; exact .pure none ()

private theorem forget_writer {Result : Type} {pending : Option (HostState sig)}
    {program : Session grow sig Result} (safe : HostSafe CheckedWrite pending program) :
    HostSafe Extends pending program := by
  induction safe with
  | pure pending value => exact .pure pending value
  | op pending plain _ next => exact .op pending plain next
  | get pending _ next => exact .get pending next
  | set relation _ next => exact .set relation.1 next

theorem extends_of_steps (bindings : List (Binding sig))
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) initial labels final)
    (safe : CfgSafe Extends initial) (runSafe : RunSafe Extends labels) : Extends initial.host final.host := by
  have checked := host_safe (grow := grow) bindings
  have hostExt : HostImplSafe Extends (host (grow := grow) bindings) :=
    ⟨fun _ _ => forget_writer (checked.funcs _ _), fun _ _ _ => forget_writer (checked.embedder _ _ _),
      fun _ _ => forget_writer (checked.threadBody _ _), fun _ => forget_writer (checked.buffer _),
      fun _ => forget_writer (checked.cancel _)⟩
  have dispatchExt := HostWrite.hostSafe_dispatch hostExt Limits.spec Quirks.none ready
  induction steps with
  | refl => exact ⟨List.prefix_rfl, le_rfl⟩
  | cons first _ ih =>
    have nextSafe := HostWrite.step_cfgSafe dispatchExt first safe
      (fun program equal => runSafe program (by simp [equal]))
    have tail := ih nextSafe (fun program member => runSafe program (List.mem_cons_of_mem _ member))
    rcases HostWrite.step_host first safe with same | extended
    · rwa [same] at tail
    · exact ⟨extended.1.trans tail.1, le_trans extended.2 tail.2⟩

theorem checked_of_steps (bindings : List (Binding sig))
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels) :
    Extends initial.host final.host ∧ WriterRun initial.host.writer final.host.writer := by
  have checked := HostWrite.hostSafe_dispatch (host_safe (grow := grow) bindings) Limits.spec Quirks.none ready
  induction steps with
  | refl => exact ⟨⟨List.prefix_rfl, le_rfl⟩, .refl _⟩
  | cons first _ ih =>
    have nextSafe := HostWrite.step_cfgSafe checked first safe (fun program equal => runSafe program (by simp [equal]))
    have tail := ih nextSafe (fun program member => runSafe program (List.mem_cons_of_mem _ member))
    rcases HostWrite.step_host first safe with same | extended
    · rwa [same] at tail
    · exact ⟨⟨extended.1.1.trans tail.1.1, le_trans extended.1.2 tail.1.2⟩, .cons extended.2 tail.2⟩

theorem owner_retired {before after : Stored.OwnedMemory.Claims.State sig} {id : HandleObjId}
    (run : WriterRun before after) (retired : before.retiredOwner id) : after.retiredOwner id := by
  induction run with
  | refl => exact retired
  | cons step _ ih =>
    apply ih
    cases step with
    | same => exact retired
    | publish _ registered => exact Stored.OwnedMemory.Claims.register_retains_retirement registered retired
    | spend update =>
      cases update with
      | endpoint => exact retired
      | owner =>
        refine ⟨retired.1, fun member => retired.2 ?_⟩
        obtain ⟨receipt, contained, equal⟩ := List.mem_map.mp member
        exact List.mem_map.mpr ⟨receipt, (List.mem_filter.mp contained).1, equal⟩

theorem endpoint_publications {before after : Stored.OwnedMemory.Claims.State sig}
    (run : WriterRun before after) :
    ∃ roots, after.accepted = roots ++ before.accepted ∧
      ∀ id ∈ after.endpoints, id ∈ before.endpoints ∨
        id ∈ roots.flatMap Stored.OwnedMemory.Claims.rootEndpoints := by
  induction run with
  | refl => exact ⟨[], rfl, fun _ member => .inl member⟩
  | cons step _ ih =>
    obtain ⟨roots, accepted, support⟩ := ih
    cases step with
    | same => exact ⟨roots, accepted, support⟩
    | publish tree registered =>
      have published := Stored.OwnedMemory.Claims.register_claims registered
      refine ⟨roots ++ [tree], by simp [accepted, published.1, List.append_assoc], ?_⟩
      intro id member
      rcases support id member with prior | newer
      · rw [published.2.2] at prior
        rcases List.mem_append.mp prior with atRoot | old
        · exact .inr (by simp [List.flatMap_append, atRoot])
        · exact .inl old
      · exact .inr (by simp [List.flatMap_append, newer])
    | spend update =>
      refine ⟨roots, ?_, ?_⟩
      · rw [accepted]; cases update <;> rfl
      · intro id member
        rcases support id member with earlier | published
        · apply Or.inl
          cases update with
          | owner => exact earlier
          | endpoint => exact (List.mem_filter.mp earlier).1
        · exact .inr published

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript
