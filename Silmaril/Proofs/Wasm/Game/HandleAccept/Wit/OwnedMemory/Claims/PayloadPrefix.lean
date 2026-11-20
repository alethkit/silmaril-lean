module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Local.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims

variable {E : CoreEngine} {Host Result Next : Type}
  {profile : ProfileKind} {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)}

private theorem chain {before middle after : Config E Host} {front back : List (Label E Host)}
    (left : Steps profile ready dispatch before front middle) (right : Steps profile ready dispatch middle back after) :
    Steps profile ready dispatch before (front ++ back) after := by
  induction left with
  | refl => exact right
  | cons step _ ih => exact .cons step (ih right)

private theorem silent {labels : List (Label E Host)} (allTau : ∀ label ∈ labels, label = .tau) :
    visible labels = [] := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
    have head := allTau label (List.mem_cons_self ..)
    simp only [head, visible, List.filter_cons, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun other member => allTau other (List.mem_cons_of_mem _ member))

private theorem visible_append (front back : List (Label E Host)) :
    visible (front ++ back) = visible front ++ visible back := List.filter_append ..

private theorem trace {outcome : Except TrapReason Result} {labels : List (Label E Host)}
    (valid : LocalLeafLabels outcome labels) :
    visible labels = match outcome with | .ok _ => [] | .error reason => [.trap reason] := by
  cases outcome with
  | ok _ =>
    apply silent
    intro label member
    have test := List.all_eq_true.mp valid label member
    cases label <;> simp_all
  | error reason =>
    obtain ⟨count, rfl⟩ := valid
    have prefixSilent : visible (List.replicate count (.tau : Label E Host)) = [] :=
      silent (fun label member => (List.eq_of_mem_replicate member))
    rw [visible_append, prefixSilent, List.nil_append]
    rfl

private theorem returned (value : Result) :
    Compare profile ready dispatch (pure (.ok value)) (pure value) := by
  intro left right same checkCursor canonCursor _ checkNext canonNext checkAt canonAt
  exact ⟨.returned value, [], [], left, right, .refl _, .refl _, same, rfl, checkAt, canonAt⟩

theorem sequential {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (first : Compare profile ready dispatch checked canonical)
    (checkTail : Result → P E Host (Except RecordLower.Issue Next)) (canonTail : Result → P E Host Next)
    (rest : ∀ value, Compare profile ready dispatch (checkTail value) (canonTail value)) :
    Compare profile ready dispatch
      (checked >>= fun result => match result with | .error issue => pure (.error issue) | .ok value => checkTail value)
      (canonical >>= canonTail) := by
  intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  let checkSuffix := fun (result : Except RecordLower.Issue Result) =>
    (match result with | .error issue => pure (.error issue) | .ok value => checkTail value) >>= checkNext
  let canonSuffix := fun value => canonTail value >>= canonNext
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, labels, status⟩ :=
    first left right same checkCursor canonCursor sameThread checkSuffix canonSuffix
      (by simpa only [checkSuffix, Prog.bind_eq, Prog.bind_assoc] using checkAt)
      (by simpa only [canonSuffix, Prog.bind_eq, Prog.bind_assoc] using canonAt)
  cases outcome with
  | refused issue => exact ⟨.refused issue, chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | trapped reason => exact ⟨.trapped reason, chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | returned value =>
    obtain ⟨outcome, chk', ref', left'', right'', runChk', runRef', stores', labels', status'⟩ :=
      rest value left' right' stores checkCursor canonCursor sameThread checkNext canonNext status.1 status.2
    refine ⟨outcome, chk ++ chk', ref ++ ref', left'', right'', chain runChk runChk', chain runRef runRef',
      stores', ?_, ?_⟩
    · rw [visible_append, visible_append, labels, labels']
    · cases outcome with
      | returned _ | refused _ => exact status'
      | trapped reason =>
        obtain ⟨emptyCheck, emptyCanon, leading, last⟩ := status'
        refine ⟨emptyCheck, emptyCanon, visible ref ++ leading, ?_⟩
        rw [visible_append, last, List.append_assoc]

private theorem mapResult {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (compare : Compare profile ready dispatch checked canonical) (resultMap : Result → Next)
    (issueMap : RecordLower.Issue → RecordLower.Issue) :
    Compare profile ready dispatch (do return ((← checked).map resultMap).mapError issueMap)
      (do return resultMap (← canonical)) := by
  intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, labels, status⟩ :=
    compare left right same checkCursor canonCursor sameThread
      (fun result => checkNext ((result.map resultMap).mapError issueMap)) (fun value => canonNext (resultMap value))
      (by simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using checkAt) (by
        simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using canonAt)
  cases outcome with
  | returned value => exact ⟨.returned (resultMap value), chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | refused issue => exact ⟨.refused (issueMap issue), chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | trapped reason => exact ⟨.trapped reason, chk, ref, left', right', runChk, runRef, stores, labels, status⟩

private theorem map_id (result : Except RecordLower.Issue Result) : result.map id = result := by
  cases result <;> rfl

private theorem mapError_id (result : Except RecordLower.Issue Result) : result.mapError id = result := by
  cases result <;> rfl

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {scheduledReady : HostReady (HostState sig)}
  {scheduledDispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

theorem handle (destination : RecordDestination) (inst : InstId) (item : Field) (isHandle : CanonicalHandle item)
    (index : Nat) (output : Lower.Output) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.checkedLeaf recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item index output)
      (CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst) destination.width item output) := by
  intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  rcases checkCursor with ⟨thread, checkFrames, checkRest⟩
  rcases canonCursor with ⟨otherThread, canonFrames, canonRest⟩
  change thread = otherThread at sameThread
  subst otherThread
  have paired := RecordDestination.compare_handle_leaf (profile := profile) (ready := scheduledReady)
    (dispatch := scheduledDispatch) same destination inst item isHandle index output checkNext canonNext checkAt canonAt
  cases verdict : liveLeafPlan left.store left.host.writer index item with
  | error issue =>
    rw [verdict] at paired
    obtain ⟨labels, allTau, steps⟩ := paired
    exact ⟨.refused issue, labels, [], _, right, steps, .refl right, same, silent allTau, rfl⟩
  | ok plan =>
    rw [verdict] at paired
    obtain ⟨reached, outcome, leading, chk, ref, allTau, checkTrace, canonTrace, checkRun, canonRun⟩ := paired
    have labels : visible (leading ++ chk) = visible ref := by
      cases outcome <;> rw [visible_append, silent allTau, List.nil_append, trace checkTrace, trace canonTrace]
    cases outcome with
    | ok value => exact ⟨.returned value, _, _, _, _, checkRun, canonRun, rfl, labels, rfl, rfl⟩
    | error reason =>
      exact ⟨.trapped reason, _, _, _, _, checkRun, canonRun, rfl, labels, rfl, rfl, [], trace canonTrace⟩

mutual
theorem flatField (destination : RecordDestination) (inst : InstId) (item : Field)
    (fragment : HandleField item) (index : Nat) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item index .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item .flat) := by
  cases item with
  | aggregate type children | fixed type size children =>
    rw [HandleField] at fragment
    have compared := flatFields destination inst children fragment 0
    rw [Record.Effects.field, CanonicalTree.field]
    simpa only [Lower.Output.Result, map_id, id_eq, Prog.bind_eq, Prog.pure_eq, Prog.bind_pure] using
      mapResult compared id (.nested index)
  | owner _ | endpoint _ _ _ | context _ =>
    rw [Record.Effects.field, CanonicalTree.field]
    exact handle destination inst _ fragment index .flat
  | data _ _ | dynamic _ _ _ | sum _ _ _ _ => exact False.elim fragment
termination_by structural item

theorem flatFields (destination : RecordDestination) (inst : InstId) (items : List Field)
    (fragment : HandleFields items) (index : Nat) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.flat recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width items index)
      (CanonicalTree.flat Limits.spec Quirks.none (destination.context inst) destination.width items) := by
  cases items with
  | nil => rw [Record.Effects.flat, CanonicalTree.flat]; exact returned []
  | cons child rest =>
    rw [HandleFields] at fragment
    rw [Record.Effects.flat, CanonicalTree.flat]
    have first := flatField destination inst child fragment.1 index
    have later := flatFields destination inst rest fragment.2 (index + 1)
    have composed := sequential first _ _ (fun words => by
      let headWords : List FlatValue := words
      simpa only [mapError_id] using mapResult later (headWords ++ ·) id)
    convert composed using 2 <;> try rfl
    funext verdict
    cases verdict <;> rfl
termination_by structural items
end

private theorem prependCheck {left entered right : Config E Host} {labels : List (Label E Host)}
    {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (entry : Steps profile ready dispatch left labels entered) (allTau : ∀ label ∈ labels, label = .tau)
    (continued : Reaches profile ready dispatch entered right checkCursor canonCursor checkNext canonNext) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext := by
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, observations, status⟩ := continued
  refine ⟨outcome, labels ++ chk, ref, left', right', chain entry runChk, runRef, stores, ?_, ?_⟩
  · rw [visible_append, silent allTau, List.nil_append, observations]
  · cases outcome <;> exact status

theorem compiledFlat (left right : Config (core3 grow) (HostState sig)) (sameStore : left.store = right.store)
    (destination : RecordDestination) (inst : InstId) (tag : sig.Tag)
    (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat} (children : Fin arity → OwnedMemory.Tree sig)
    (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload .flat = .ok (field, plan)) (fragment : HandleField field)
    (checked : destination.check left.store = .ok ()) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (sameThread : checkCursor.thread = canonCursor.thread)
    (checkNext : Except RecordLower.Issue (List FlatValue) → Session grow sig (Ret (core3 grow)))
    (canonNext : List FlatValue → Session grow sig (Ret (core3 grow)))
    (checkAt : left.ctl = checkCursor.control (Record.Effects.lowerTree recordClaims Limits.spec Quirks.none
      (destination.context inst) (.tag ⟨tag, payload⟩ arity children) .flat >>= checkNext))
    (canonAt : right.ctl = canonCursor.control (lowerFlatAt Limits.spec Quirks.none (destination.context inst)
      destination.width payload.val.value (sig.payload tag) >>= canonNext)) :
    Reaches profile scheduledReady scheduledDispatch left right checkCursor canonCursor checkNext canonNext := by
  have start := destination.compiled_payload_effects (profile := profile) (ready := scheduledReady)
    (dispatch := scheduledDispatch) left inst tag payload .flat field plan checkNext compiled checked checkAt
  have reference := destination.compiled_payload_reference (grow := grow) (World := HostState sig)
    inst (sig.payload tag) payload .flat field plan compiled
  have canonField : right.ctl = canonCursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width field .flat >>= canonNext) := by
    rw [reference]
    exact canonAt
  have entry := start.2.2.2
  cases verdict : Record.prepare left.store left.host.writer field.objects with
  | error issue =>
    rw [verdict] at entry
    exact ⟨.refused issue, [.tau, .tau], [], _, right, entry, .refl right, sameStore, rfl, rfl⟩
  | ok passed =>
    cases passed
    rw [verdict] at entry
    cases fits : Lower.fits Quirks.none destination.encoding destination.width (sig.payload tag) payload.val.value with
    | false =>
      simp only [fits, Bool.not_false, ↓reduceIte] at entry
      exact ⟨.refused (.preflight (.abi .allocationPrecondition)), [.tau, .tau, .tau], [], _, right,
        entry, .refl right, sameStore, rfl, rfl⟩
    | true =>
      simp only [fits, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at entry
      let entered := { left with ctl := checkCursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width field 0 .flat >>= checkNext) }
      have continued := flatField (profile := profile) (scheduledReady := scheduledReady)
        (scheduledDispatch := scheduledDispatch) destination inst field fragment 0 entered right sameStore
        checkCursor canonCursor sameThread checkNext canonNext rfl canonField
      exact prependCheck entry (by simp) continued

theorem parkedFlat (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (handleWord : BitVec IntType.i32.width) (destination : RecordDestination) (inst : InstId) (schema : TypeOf)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat}
    (children : Fin arity → OwnedMemory.Tree sig) (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload .flat = .ok (field, plan)) (fragment : HandleField field)
    (start reference : Config (core3 grow) (HostState sig)) (sameStore : start.store = reference.store)
    (canonCursor : Cursor (E := core3 grow) (HostState sig)) (canonNext : List FlatValue → Session grow sig (Ret (core3 grow)))
    {thread core continuation segments rest} (sameThread : thread = canonCursor.thread)
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) [.int .i32 handleWord])
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, .giveFlat destination schema⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Endpoints.Core.childFromHistory start.host.writer.accepted handleWord =
      some (.tag ⟨tag, payload⟩ arity children))
    (schemaChecked : rootHasSchema (.tag ⟨tag, payload⟩ arity children) schema = true)
    (canonicalAt : reference.ctl = canonCursor.control (lowerFlatAt Limits.spec Quirks.none (destination.context inst)
      destination.width payload.val.value (sig.payload tag) >>= canonNext)) :
    Reaches profile scheduledReady (specDispatch scheduledReady (host (grow := grow) bindings)) start reference
      ⟨thread, .core core continuation :: segments, rest⟩ canonCursor
      (flatReply destination schema start.host.nextTicket) canonNext := by
  let route := GiveEffectRoute.flat schema
  let tree : OwnedMemory.Tree sig := .tag ⟨tag, payload⟩ arity children
  let entered := { start with
    host := start.host.enter name type (route.args handleWord)
    ctl := ⟨thread, .prog (route.run destination inst tree start.host.nextTicket),
      .core core continuation :: segments⟩ :: rest }
  obtain ⟨labels, allTau, run⟩ := route.parked bindings name type handleWord inst destination tree
    start thread profile scheduledReady parked calling linked caller mayLeave destinationChecked selected schemaChecked
  have continued := compiledFlat (profile := profile) (scheduledReady := scheduledReady)
    (scheduledDispatch := specDispatch scheduledReady (host bindings)) entered reference sameStore
    destination inst tag payload children field plan compiled fragment destinationChecked
    ⟨thread, .core core continuation :: segments, rest⟩ canonCursor sameThread
    (flatReply destination schema start.host.nextTicket) canonNext rfl canonicalAt
  exact prependCheck run (fun label member => by
    have test := List.all_eq_true.mp allTau label member
    cases label <;> simp_all) continued

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix
