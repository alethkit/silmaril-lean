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
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims (State)
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

theorem write_completion_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (reply : Event × List FlatValue)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> writeCompletion reply), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.record reply.1
        ctl := ⟨thread, .prog (.pure (.flat reply.2)), segments⟩ :: rest } :=
  .cons (.hostGet pending) (.cons (.hostSet rfl) (.refl _))

theorem finish_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig)))
    (ticket : Nat) (result : Except Issue Nat)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> finish ticket result), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.record (completion ticket result).1
        ctl := ⟨thread, .prog (.pure (.flat (completion ticket result).2)), segments⟩ :: rest } :=
  write_completion_steps config thread segments rest _ pending

private theorem steps_append {first middle last : Config (core3 grow) (HostState sig)}
    {earlier later : List (Label (core3 grow) (HostState sig))}
    (started : Steps prof ready dispatch first earlier middle) (continued : Steps prof ready dispatch middle later last) :
    Steps prof ready dispatch first (earlier ++ later) last := by
  induction started with
  | refl => exact continued
  | cons step _ ih => exact .cons step (ih continued)

private theorem accept_load_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (loadNode : Stored.OwnedMemory.Claims.Core.World grow sig →
      CStore (core3 grow) × Except Stored.OwnedMemory.Claims.Core.Issue (Stored.OwnedMemory.Tree sig))
    (updated : CStore (core3 grow))
    (loaded : Except Stored.OwnedMemory.Claims.Core.Issue (Stored.OwnedMemory.Tree sig))
    (outcome : loadNode ⟨config.store, config.host.writer⟩ = (updated, loaded))
    (pending : config.ctl = ⟨thread,
      .prog (.flat <$> (do finish ticket (← acceptWith ticket loadNode))), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau]
      { config with
        store := updated
        ctl := ⟨thread, .prog (.flat <$> ((match loaded with
          | .error issue => pure (.error (.accept issue))
          | .ok tree => publishRoot ticket tree) >>= finish ticket)), segments⟩ :: rest } := by
  refine .cons (.hostGet pending) (.cons (.get rfl) ?_)
  change Steps prof ready dispatch
    { config with ctl := ⟨thread, .prog (.flat <$> ((do
        let outcome := loadNode ⟨config.store, config.host.writer⟩
        modifyStore fun _ => outcome.1
        match outcome.2 with
        | .error reason => pure (.error (.accept reason))
        | .ok tree => publishRoot ticket tree) >>= finish ticket)), segments⟩ :: rest } _ _
  rw [outcome]
  exact .cons (.modify rfl) (.refl _)

theorem accept_refusal_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (loadNode : Stored.OwnedMemory.Claims.Core.World grow sig →
      CStore (core3 grow) × Except Stored.OwnedMemory.Claims.Core.Issue (Stored.OwnedMemory.Tree sig))
    (updated : CStore (core3 grow)) (issue : Stored.OwnedMemory.Claims.Core.Issue)
    (refused : loadNode ⟨config.store, config.host.writer⟩ = (updated, .error issue))
    (pending : config.ctl = ⟨thread,
      .prog (.flat <$> (do finish ticket (← acceptWith ticket loadNode))), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau]
      { config with
        store := updated
        host := config.host.record (.refused ticket (.accept issue))
        ctl := ⟨thread, .prog (.pure (.flat [i32Flat 1, i32Flat 0])), segments⟩ :: rest } :=
  steps_append (accept_load_steps config thread segments rest ticket loadNode updated (.error issue) refused pending)
    (finish_steps _ thread segments rest ticket (.error (.accept issue)) rfl)

theorem accept_success_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (loadNode : Stored.OwnedMemory.Claims.Core.World grow sig →
      CStore (core3 grow) × Except Stored.OwnedMemory.Claims.Core.Issue (Stored.OwnedMemory.Tree sig))
    (updated : CStore (core3 grow)) (tree : Stored.OwnedMemory.Tree sig) (writer : State sig)
    (loaded : loadNode ⟨config.store, config.host.writer⟩ = (updated, .ok tree))
    (registered : config.host.writer.register tree = .ok writer)
    (pending : config.ctl = ⟨thread,
      .prog (.flat <$> (do finish ticket (← acceptWith ticket loadNode))), segments⟩ :: rest) :
    let handle := (BitVec.ofNat 32 writer.accepted.length).toNat
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau, .tau, .tau]
      { config with
        store := updated
        host := (({ config.host with writer } : HostState sig).record (.published ticket handle)).record
          (.returned ticket handle)
        ctl := ⟨thread, .prog (.pure (.flat [i32Flat 0, i32Flat handle])), segments⟩ :: rest } := by
  dsimp only
  refine steps_append (accept_load_steps config thread segments rest ticket loadNode updated (.ok tree) loaded pending) ?_
  refine .cons (.hostGet rfl) ?_
  change Steps prof ready dispatch
    { config with store := updated, ctl := ⟨thread, .prog (.flat <$> ((match config.host.writer.register tree with
      | .error issue => pure (.error (.accept (.claims issue)))
      | .ok writer => do
        hostSet (({ config.host with writer } : HostState sig).record
          (.published ticket (BitVec.ofNat 32 writer.accepted.length).toNat))
        return .ok (BitVec.ofNat 32 writer.accepted.length).toNat) >>= finish ticket)), segments⟩ :: rest } _ _
  rw [registered]
  exact .cons (.hostSet rfl) (finish_steps _ thread segments rest ticket (.ok _) rfl)

theorem accept_registration_refusal_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (loadNode : Stored.OwnedMemory.Claims.Core.World grow sig →
      CStore (core3 grow) × Except Stored.OwnedMemory.Claims.Core.Issue (Stored.OwnedMemory.Tree sig))
    (updated : CStore (core3 grow)) (tree : Stored.OwnedMemory.Tree sig)
    (issue : Stored.OwnedMemory.Claims.Issue)
    (loaded : loadNode ⟨config.store, config.host.writer⟩ = (updated, .ok tree))
    (rejected : config.host.writer.register tree = .error issue)
    (pending : config.ctl = ⟨thread,
      .prog (.flat <$> (do finish ticket (← acceptWith ticket loadNode))), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau, .tau]
      { config with
        store := updated
        host := config.host.record (.refused ticket (.accept (.claims issue)))
        ctl := ⟨thread, .prog (.pure (.flat [i32Flat 1, i32Flat 0])), segments⟩ :: rest } := by
  refine steps_append (accept_load_steps config thread segments rest ticket loadNode updated (.ok tree) loaded pending) ?_
  refine .cons (.hostGet rfl) ?_
  change Steps prof ready dispatch
    { config with store := updated, ctl := ⟨thread, .prog (.flat <$> ((match config.host.writer.register tree with
      | .error issue => pure (.error (.accept (.claims issue)))
      | .ok writer => do
        hostSet (({ config.host with writer } : HostState sig).record
          (.published ticket (BitVec.ofNat 32 writer.accepted.length).toNat))
        return .ok (BitVec.ofNat 32 writer.accepted.length).toNat) >>= finish ticket)), segments⟩ :: rest } _ _
  rw [rejected]
  exact finish_steps _ thread segments rest ticket (.error (.accept (.claims issue))) rfl

theorem flatCompletion_type (ticket : Nat) (shape : List NumType) (result : Except Issue (List FlatValue)) :
    (flatCompletion ticket shape result).2.map Stored.flatType = .int .i32 :: shape := by
  have zeroTypes : (shape.map zeroWord).map Stored.flatType = shape := by
    induction shape with
    | nil => rfl
    | cons head tail ih =>
      change Stored.flatType (zeroWord head) :: (tail.map zeroWord).map Stored.flatType = head :: tail
      rw [ih]
      cases head with
      | int kind => cases kind <;> rfl
      | float kind => cases kind <;> rfl
  cases result with
  | error issue => exact congrArg (.int .i32 :: ·) zeroTypes
  | ok values =>
    by_cases typed : values.map Stored.flatType = shape
    · simp only [flatCompletion, ite_eq_left typed]
      exact congrArg (.int .i32 :: ·) typed
    · simp only [flatCompletion, ite_eq_right typed]
      exact congrArg (.int .i32 :: ·) zeroTypes

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

private theorem publication_refl (state : HostState sig) : PublicationDelta state state :=
  ⟨[], by simp, by simp, by simp⟩

private theorem publication_trans {first middle last : HostState sig}
    (earlier : PublicationDelta first middle) (later : PublicationDelta middle last) :
    PublicationDelta first last := by
  obtain ⟨earlierEntries, middleEntries, middleCount, earlierHandle⟩ := earlier
  obtain ⟨suffix, lastEntries, lastCount, laterHandle⟩ := later
  refine ⟨earlierEntries ++ suffix, by simp [lastEntries, middleEntries, List.append_assoc],
    by simp [lastCount, middleCount, Nat.add_assoc], ?_⟩
  intro index ticket handle entry
  by_cases inEarlier : index < earlierEntries.length
  · rw [List.getElem?_append_left inEarlier] at entry
    exact earlierHandle index ticket handle entry
  · rw [List.getElem?_append_right (Nat.le_of_not_gt inEarlier)] at entry
    have position : middle.writer.accepted.length + (index - earlierEntries.length) + 1 =
        first.writer.accepted.length + index + 1 := by omega
    simpa only [position] using laterHandle (index - earlierEntries.length) ticket handle entry

private theorem record_safe (state : HostState sig) (event : Event) (notPublication : event.publication = none) :
    CheckedWrite state (state.record event) :=
  ⟨⟨by simp [HostState.transcript, HostState.record], le_rfl⟩, .same _,
    ⟨[], by simp [HostState.publications, HostState.transcript, HostState.record, notPublication],
      by simp [HostState.record], by simp⟩⟩

private theorem spend_safe (update : Stored.OwnedMemory.Claims.Spend) :
    Safe ((claims (grow := grow) (sig := sig)).spend update) :=
  .get none fun state => .set ⟨⟨List.prefix_rfl, le_rfl⟩, .spend _ _,
    by cases update <;> exact publication_refl state⟩ (.pure none ())

private theorem read_safe : Safe ((claims (grow := grow) (sig := sig)).read) :=
  .get none fun state => .pure _ state.writer

private theorem publish_safe (ticket : Nat) (tree : Stored.OwnedMemory.Tree sig) :
    Safe (publishRoot (grow := grow) ticket tree) := by
  refine .get none fun current => ?_
  change HostSafe CheckedWrite (some current) ((match current.writer.register tree with
    | .error issue => pure (.error (.accept (.claims issue)))
    | .ok writer => do
      let handle := (BitVec.ofNat 32 writer.accepted.length).toNat
      hostSet (({ current with writer } : HostState sig).record (.published ticket handle))
      return .ok handle) : Session grow sig (Except Issue Nat))
  split <;> rename_i writer registered
  · exact .pure (some current) _
  · refine .set ⟨⟨by simp [HostState.transcript, HostState.record], le_rfl⟩, .publish _ registered, ?_⟩
      (.pure none _)
    have accepted := (Stored.OwnedMemory.Claims.register_claims registered).1
    refine ⟨[(ticket, (BitVec.ofNat 32 writer.accepted.length).toNat)],
      by simp [HostState.publications, HostState.transcript, HostState.record, Event.publication],
      by simp [HostState.record, accepted], ?_⟩
    intro index eventTicket handle entry
    cases index with
    | zero => simpa [accepted] using (Option.some.inj entry).symm |> congrArg Prod.snd
    | succ index => simp at entry

private theorem accept_with_safe (ticket : Nat)
    (loadNode : Stored.OwnedMemory.Claims.Core.World grow sig →
      CStore (core3 grow) × Except Stored.OwnedMemory.Claims.Core.Issue (Stored.OwnedMemory.Tree sig)) :
    Safe (acceptWith ticket loadNode) := by
  unfold acceptWith
  refine HostWrite.bind (readOnly P.Inv.hostGet) fun state => ?_
  refine HostWrite.bind (readOnly P.Inv.getStore) fun reference => ?_
  refine HostWrite.bind (readOnly (P.Inv.modifyStore (fun _ _ => trivial))) fun _ => ?_
  split
  · exact .pure none _
  · exact publish_safe _ _

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

private theorem give_flat_safe (inst : InstId) (destination : RecordDestination) (payload : Stored.TypeOf)
    (args : List FlatValue) : Safe (giveFlat (grow := grow) (sig := sig) inst destination payload args) := by
  unfold giveFlat
  refine HostWrite.bind (readOnly P.Inv.currentInst?) fun current => ?_
  refine HostWrite.bind (readOnly P.Inv.getStore) fun store => ?_
  dsimp only
  split
  · exact .pure none _
  · split
    · refine HostWrite.bind (readOnly P.Inv.getStore) fun store => ?_
      split
      · exact .pure none _
      · refine HostWrite.bind (.get none fun _ => .pure _ _) fun selected => ?_
        cases selected with
        | none => exact .pure none _
        | some tree =>
          change Safe (if (!rootHasSchema tree payload) = true then pure (Except.error Issue.wrongPayloadType) else _)
          split
          · exact .pure none _
          · exact HostWrite.bind (lower_payload_safe _ tree .flat) fun _ => .pure none _
    · exact .pure none _

private theorem invoke_safe (ticket : Nat) (binding : Binding sig) (args : List FlatValue) :
    Safe (Stored.OwnedMemory.Claims.Core.Scheduled.invoke (grow := grow) ticket binding args) := by
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
      · exact accept_with_safe _ _
    case acceptFlat =>
      split
      · exact .pure none _
      · exact accept_with_safe _ _
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
    case giveFlat => exact .pure none _

private theorem write_completion_safe (reply : Event × List FlatValue) (notPublication : reply.1.publication = none) :
    Safe (writeCompletion (grow := grow) (sig := sig) reply) :=
  .get none fun state => .set (record_safe state _ notPublication) (.pure none _)

private theorem finish_safe (ticket : Nat) (result : Except Issue Nat) :
    Safe (finish (grow := grow) (sig := sig) ticket result) :=
  write_completion_safe _ (by cases result <;> rfl)

private theorem flat_completion_safe (ticket : Nat) (shape : List NumType)
    (result : Except Issue (List FlatValue)) : Safe (writeCompletion (grow := grow) (sig := sig)
      (flatCompletion ticket shape result)) := by
  apply write_completion_safe
  unfold flatCompletion
  split
  · rfl
  · split <;> rfl

private theorem binding_trap_safe (ticket : Nat) (issue : Issue) :
    Safe (rejectBinding (grow := grow) (sig := sig) ticket issue) :=
  .get none fun state => .set (record_safe state _ rfl) (readOnly (P.Inv.trap _))

private theorem route_safe (ticket : Nat) (bindings : List (Binding sig)) (name : String)
    (type : V1.FuncType) (args : List FlatValue) : Safe (route (grow := grow) ticket bindings name type args) := by
  unfold route
  split
  · exact binding_trap_safe _ _
  · split
    · exact binding_trap_safe _ _
    · split
      · exact HostWrite.bind (give_flat_safe _ _ _ _) (flat_completion_safe _ _)
      · exact HostWrite.bind (invoke_safe _ _ _) (finish_safe _)
  · exact binding_trap_safe _ _

private theorem host_safe (bindings : List (Binding sig)) :
    HostImplSafe CheckedWrite (host (grow := grow) bindings) := by
  constructor
  · intro name caller; exact readOnly (P.Inv.internal _)
  · intro name type args
    refine .get none fun state => .set ?_ (route_safe _ _ _ _ _)
    exact ⟨⟨by simp [HostState.enter, HostState.transcript], Nat.le_succ _⟩, .same _,
      ⟨[], by simp [HostState.publications, HostState.enter, HostState.transcript, Event.publication],
        by simp [HostState.enter], by simp⟩⟩
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
    Extends initial.host final.host ∧ WriterRun initial.host.writer final.host.writer ∧
      PublicationDelta initial.host final.host := by
  have checked := HostWrite.hostSafe_dispatch (host_safe (grow := grow) bindings) Limits.spec Quirks.none ready
  induction steps with
  | refl => exact ⟨⟨List.prefix_rfl, le_rfl⟩, .refl _, publication_refl _⟩
  | cons first _ ih =>
    have nextSafe := HostWrite.step_cfgSafe checked first safe (fun program equal => runSafe program (by simp [equal]))
    have tail := ih nextSafe (fun program member => runSafe program (List.mem_cons_of_mem _ member))
    rcases HostWrite.step_host first safe with same | extended
    · rwa [same] at tail
    · exact ⟨⟨extended.1.1.trans tail.1.1, le_trans extended.1.2 tail.1.2⟩, .cons extended.2.1 tail.2.1,
        publication_trans extended.2.2 tail.2.2⟩

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
