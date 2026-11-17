module

public import Silmaril.Wasm.Component.DecoderBridge.MultiX.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Multi.Thms
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.ExportX
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.CallLift

/-!
# The instantiation on `MultiImpFrag` with its invariant: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi` (`FirstKX`, `LaterCoreX`,
`NodesRefX`, `ComposeX`, `ExportX`, `CallLift`).

* **`nodesRefX`** (proved): in the split fragment `MultiImpFrag`, the reference machine finishes
  the instantiation with the host log of the IR's node calls, in a configuration satisfying
  `NodesInv` (the final frame related to the reading, each node's core instance the gap image of
  its IR store after its start function);
* `nodesRef_of_X`: `Task.nodesRef` is its projection;
* `startAdequacyFrag_of_X`: **`Task.startAdequacy` on the fragment from `Task.exportRefX`** (the
  export call from the invariant);
* **`callLift`** (proved, `Multi.CallLift`): `Task.callLift`, the session call of an option-less
  lift of `func() -> u32` from a host-ready configuration (nesting depth `0`, which `NodesInv`
  records: the instantiation's invariant tracks depth `1` inside the host's program);
* `exportRefX_of`: **`Task.exportRefX` from `Task.exportIR`, `Task.coreRunShared` and
  `Task.callLift`**; `startAdequacyFrag_of_IR`: the start goal from the first two; `startAdequacyFrag_of_parts`, `starts_of_parts`: the start goal and the
  `starts.wasm` instance from these three pieces;
* `starts_of_X`: the reference half of `InstTestsRef.starts_agree`, derived from the IR's run of
  `starts.wasm` through `Task.exportRefX`. (The conclusion is also proved unconditionally by
  executing the reference machine, `InstTestsRef.starts_agree`.)

This is the split fragment only (function-only imports wired to `canon lower`ed component
imports, no shared memories or tables, option-less `canon lift` on flat primitive types), not
general shared memory, table or canonical ABI adequacy.
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

/-- **The instantiation on the fragment, with node ends and the invariant `NodesInv`.** -/
theorem nodesRefX : Task.nodesRefX :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.nodesRefX

/-- `Task.nodesRef` is the projection of `Task.nodesRefX`. -/
theorem nodesRef_of_X (h : Task.nodesRefX) : Task.nodesRef :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.nodesRef_of_X h

/-- **The start goal on the fragment from the export call with the invariant.** -/
theorem startAdequacyFrag_of_X (hd : Task.exportRefX) : Task.startAdequacyFrag :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.startAdequacyFrag_of_X hd

/-- **`starts.wasm` from the IR's run, given the export call with the invariant.** -/
theorem starts_of_X (hd : Task.exportRefX) :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
        ((), logOfCalls startsTrace)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  starts_of_frag (startAdequacyFrag_of_X hd)

/-- **The export call from the invariant, from the IR's export phase, the node's run in the shared
core store and the session call through `canon lift`.** -/
theorem exportRefX_of (hA : Task.exportIR) (hB : Task.coreRunShared) (hC : Task.callLift) :
    Task.exportRefX :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.exportRefX_of hA hB hC

/-- **The start goal on the fragment from the three pieces of the export call.** -/
theorem startAdequacyFrag_of_parts (hA : Task.exportIR) (hB : Task.coreRunShared)
    (hC : Task.callLift) : Task.startAdequacyFrag :=
  startAdequacyFrag_of_X (exportRefX_of hA hB hC)

/-- **`starts.wasm` from the IR's run, given the three pieces of the export call.** -/
theorem starts_of_parts (hA : Task.exportIR) (hB : Task.coreRunShared) (hC : Task.callLift) :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
        ((), logOfCalls startsTrace)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  starts_of_X (exportRefX_of hA hB hC)

/-- **The session call through `canon lift`** (from a host-ready configuration: no host code
running, no lockdown, nesting depth `0`). -/
theorem callLift : Task.callLift :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.callLift

/-- **The start goal on the fragment from the IR's export phase and the node's run in the shared
core store.** -/
theorem startAdequacyFrag_of_IR (hA : Task.exportIR) (hB : Task.coreRunShared) :
    Task.startAdequacyFrag :=
  startAdequacyFrag_of_parts hA hB callLift

end Silmaril.Wasm.Component.DecoderBridge
