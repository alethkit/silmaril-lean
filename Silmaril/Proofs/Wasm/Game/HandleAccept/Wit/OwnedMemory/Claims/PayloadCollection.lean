module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadInstall.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Collection.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadInstall.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Collection.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit

variable {grow : SingleThreaded.GrowOracle} {Host : Type}
  {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
  {before after : Machine.Config (core3 grow) Host} {trace : List (Label (core3 grow) Host)}

private theorem append_steps {first middle last : Machine.Config (core3 grow) Host} {front back}
    (prefixSteps : Machine.Steps profile ready dispatch first front middle)
    (suffixSteps : Machine.Steps profile ready dispatch middle back last) :
    Machine.Steps profile ready dispatch first (front ++ back) last := by
  induction prefixSteps with
  | refl => exact suffixSteps
  | cons step _ ih => exact .cons step (ih suffixSteps)

theorem canonical_dynamic_call (run : CoreGrowthSteps profile ready dispatch before trace after)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check before.store = .ok ())
    (element : Stored.TypeOf) (entries : List Field) (output : Stored.Lower.Output)
    (storeEntry : AddrType → Field → Nat → P (core3 grow) Host Unit)
    (finish : output.Result → P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (canonicalDynamic (destination.context inst) destination.width
      element entries storeEntry output >>= finish), segments⟩ :: rest) :
    let cx := destination.context (grow := grow) inst
    let area := layout destination.width element
    let request := Call.reallocate cx 0 0 area.alignment.bytes (entries.length * area.size)
    ∃ resume : Ret (core3 grow) → P (core3 grow) Host (Ret (core3 grow)),
      (∀ pointer, resume (.nat pointer) = (do
        let ptr ← validateListRange cx area entries.length pointer
        elementSequence (fun _ => storeEntry destination.width) entries area.size ptr 0
        let result ← ListLower.publish cx destination.width ptr entries.length output
        finish result)) ∧
      Machine.Steps profile ready dispatch after [.tau, .tau]
        { after with ctl := ⟨thread, .prog (dispatch request), .prog resume :: segments⟩ :: rest } := by
  let cx := destination.context (grow := grow) inst
  let next := fun width =>
    let area := layout width element
    allocateListRange cx area entries.length >>= fun ptr => do
      elementSequence (fun _ => storeEntry width) entries area.size ptr 0
      let result ← ListLower.publish cx destination.width ptr entries.length output
      finish result
  have widthStep := run.read_width cx rfl (destination.check_width before.store checked) next
    (by simpa only [canonicalDynamic, bind_assoc, cx, next] using focused)
  let middle := { after with ctl := ⟨thread, .prog (next destination.width), segments⟩ :: rest }
  obtain ⟨resume, agreement, callStep⟩ := listRange_call (after := middle) (profile := profile)
    (ready := ready) (dispatch := dispatch) cx (layout destination.width element) entries.length
    (fun ptr => do
      elementSequence (fun _ => storeEntry destination.width) entries (layout destination.width element).size ptr 0
      let result ← ListLower.publish cx destination.width ptr entries.length output
      finish result) rfl
  exact ⟨resume, agreement, append_steps widthStep.steps (.cons callStep (.refl _))⟩

theorem checked_dynamic_call {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination)
    (inst : InstId) (type element : Stored.TypeOf) (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (finish : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (prepared : Record.prepare reached.store reached.host.writer (Field.listObjects entries) = .ok ())
    {thread segments rest}
    (focused : reached.ctl = ⟨thread, .prog (Internal.runField Limits.spec Quirks.none (destination.context inst)
      (Record.authority recordClaims Limits.spec (destination.context inst)) destination.width
      (.dynamic type element entries) index output >>= finish), segments⟩ :: rest) :
    let cx := destination.context (grow := grow) inst
    let authority := Record.authority recordClaims Limits.spec cx
    let area := layout destination.width element
    let request := Call.reallocate cx 0 0 area.alignment.bytes (entries.length * area.size)
    ∃ resume : Ret (core3 grow) → Session grow sig (Ret (core3 grow)),
      (∀ pointer, resume (.nat pointer) = (do
        let ptr ← validateListRange cx area entries.length pointer
        let verdict ← authority.prepare (Field.listObjects entries)
        let result ← checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width
          element entries index output ptr verdict
        finish result)) ∧
      Machine.Steps profile ready dispatch reached [.tau, .tau, .tau]
        { reached with ctl := ⟨thread, .prog (dispatch request), .prog resume :: segments⟩ :: rest } := by
  let cx := destination.context (grow := grow) inst
  let authority := Record.authority (recordClaims (sig := sig)) Limits.spec cx
  let area := layout destination.width element
  let plan := Field.listObjects entries
  let onRange : Nat → Session grow sig (Ret (core3 grow)) := fun ptr => do
    let verdict ← authority.prepare plan
    let result ← checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width
      element entries index output ptr verdict
    finish result
  let next : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)) := fun verdict =>
    (match verdict with
    | .error (.preflight issue) => pure (.error (.field index (.beforeAllocation issue)))
    | .error issue => pure (.error (.nested index issue))
    | .ok () => do
      let ptr ← allocateListRange cx area entries.length
      let verdict ← authority.prepare plan
      checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width element entries index
        output ptr verdict) >>= finish
  have read : reached.ctl = ⟨thread, .prog (.op .get fun store => .op .hostGet fun current =>
    next (Record.prepare store current.writer plan)), segments⟩ :: rest := by
    rw [checked_dynamic_canon_range] at focused
    exact focused
  let middle := { reached with ctl := ⟨thread, .prog (next
    (Record.prepare reached.store reached.host.writer plan)), segments⟩ :: rest }
  have reads : Machine.Steps profile ready dispatch reached [.tau, .tau] middle :=
    .cons (.get read) (.cons (.hostGet rfl) (.refl _))
  have allocating : middle.ctl = ⟨thread, .prog (allocateListRange cx area entries.length >>= onRange),
      segments⟩ :: rest := by
    simp only [middle, plan, prepared, next, onRange, bind_assoc]
  obtain ⟨resume, agreement, callStep⟩ := listRange_call cx area entries.length onRange allocating
  exact ⟨resume, agreement, append_steps reads (.cons callStep (.refl _))⟩

theorem linked_range_resume {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    (bindings : List (Binding sig)) {initial reached : Machine.Config (core3 grow) (HostState sig)}
    {trace : List (Label (core3 grow) (HostState sig))}
    (run : Machine.Steps profile ready (specDispatch ready (host bindings)) initial trace reached)
    (growing : initial.CoreGrowing)
    (installs : ∀ {current next leading label},
      Machine.Steps profile ready (specDispatch ready (host bindings)) initial leading current →
      Step profile ready (specDispatch ready (host bindings)) current label next →
      LinkedPayloadInstall bindings current label ∨ CoreGrowthInstall (specDispatch ready (host bindings)) current label)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check initial.store = .ok ())
    (start length initialBytes : Nat) (sized : (core3 grow).memSize? initial.store.core destination.memory = some initialBytes)
    (oldBounds : start + length ≤ initialBytes) (area : Layout) (count pointer : Nat)
    (finish : Nat → Session grow sig (Ret (core3 grow))) (resume : Ret (core3 grow) → Session grow sig (Ret (core3 grow)))
    (resumes : resume (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= finish))
    {thread segments rest}
    (returned : reached.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog resume :: segments⟩ :: rest) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let trapped := fun reason => ∃ steps, Machine.Steps profile ready dispatch reached
      (List.replicate steps .tau ++ [.trap reason]) (Machine.StepDefs.trapCfg reached)
    ptrTypeIn reached.store (destination.context inst) = destination.width ∧
    ∃ bytes, (core3 grow).memSize? reached.store.core destination.memory = some bytes ∧
      initialBytes ≤ bytes ∧ start + length ≤ bytes ∧
      if pointer ≠ alignTo pointer area.alignment then trapped .unalignedPointer
      else if pointer + count * area.size ≤ bytes then
        ∃ labels, (∀ label ∈ labels, label = .tau) ∧
          Machine.Steps profile ready dispatch reached labels
            { reached with ctl := ⟨thread, .prog (finish pointer), segments⟩ :: rest }
      else trapped .outOfBounds := by
  obtain ⟨prefixSteps, _⟩ := linked_payload_prefix_growth run growing installs
  obtain ⟨_, width, bytes, memSize, monotone, valid⟩ := prefixSteps.linked_region
    (destination.context inst) rfl (destination.check_width initial.store checked) sized oldBounds
  refine ⟨width, bytes, memSize, monotone, valid, ?_⟩
  have next := destination.listRange_resume (after := reached) (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (host bindings)) inst area count pointer finish resume resumes returned
  dsimp only at next
  rw [destination.listRange_body inst area count pointer reached.store reached.host thread, memSize] at next
  by_cases aligned : pointer ≠ alignTo pointer area.alignment
  · simpa [aligned] using next
  · by_cases fits : pointer + count * area.size ≤ bytes <;> simpa [aligned, fits] using next

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection
