module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Collection.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

variable {grow : SingleThreaded.GrowOracle} {Host : Type}
  {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
  {before after : Machine.Config (core3 grow) Host} {trace : List (Label (core3 grow) Host)}

/-- The canonical width read at a reached collection cursor supplies the same
layout as the linked destination. The two steps install the exact realloc
request and save validation, element stores, and descriptor publication. -/
theorem RecordDestination.canonical_dynamic_call (run : CoreGrowthSteps profile ready dispatch before trace after)
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
        let result ← Endpoints.ListLower.publish cx destination.width ptr entries.length output
        finish result)) ∧
      Machine.Steps profile ready dispatch after [.tau, .tau]
        { after with ctl := ⟨thread, .prog (dispatch request), .prog resume :: segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection.canonical_dynamic_call
    run destination inst checked element entries output storeEntry finish focused

/-- After the checked traversal's initial live dry run succeeds, it installs
the same realloc request. Its continuation inserts plan revalidation after
canonical range validation and before either element or descriptor writes. -/
theorem RecordDestination.checked_dynamic_call {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination)
    (inst : InstId) (type element : Stored.TypeOf) (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (finish : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
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
        { reached with ctl := ⟨thread, .prog (dispatch request), .prog resume :: segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection.checked_dynamic_call
    reached destination inst type element entries index output finish prepared focused

/-- A checked return from realloc validates range and the live plan before
entering element traversal. Both branches retain the reached store and
writer up to this point, not the state before the callback. -/
theorem RecordDestination.checked_dynamic_recheck {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination)
    (inst : InstId) (element : Stored.TypeOf) (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (pointer : Nat) (finish : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (resume : Ret (core3 grow) → Session grow sig (Ret (core3 grow)))
    (resumes : resume (.nat pointer) = (do
      let cx := destination.context inst
      let authority := Record.authority recordClaims Limits.spec cx
      let ptr ← validateListRange cx (layout destination.width element) entries.length pointer
      let verdict ← authority.prepare (Field.listObjects entries)
      let result ← checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width
        element entries index output ptr verdict
      finish result)) {thread segments rest}
    (returned : reached.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog resume :: segments⟩ :: rest)
    (aligned : pointer = alignTo pointer (layout destination.width element).alignment) {bytes : Nat}
    (sized : (core3 grow).memSize? reached.store.core destination.memory = some bytes)
    (bounds : pointer + entries.length * (layout destination.width element).size ≤ bytes) :
    let cx := destination.context (grow := grow) inst
    let authority := Record.authority recordClaims Limits.spec cx
    ∃ labels, (∀ label ∈ labels, label = .tau) ∧
      Machine.Steps profile ready dispatch reached labels
        { reached with ctl := ⟨thread, .prog (checkedDynamicContinue Limits.spec Quirks.none cx authority
            destination.width element entries index output pointer
            (Record.prepare reached.store reached.host.writer (Field.listObjects entries)) >>= finish),
          segments⟩ :: rest } :=
  destination.listRange_recheck reached inst (layout destination.width element) entries.length pointer
    (Field.listObjects entries) (fun ptr verdict => checkedDynamicContinue Limits.spec Quirks.none
      (destination.context inst) (Record.authority recordClaims Limits.spec (destination.context inst))
      destination.width element entries index output ptr verdict >>= finish) resume resumes returned aligned sized bounds

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
