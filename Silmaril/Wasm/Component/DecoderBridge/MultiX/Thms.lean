module

public import Silmaril.Wasm.Component.DecoderBridge.MultiX.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Multi.Thms
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.ComposeX

/-!
# The instantiation on `MultiImpFrag` with its invariant: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi` (`FirstKX`, `LaterCoreX`,
`NodesRefX`, `ComposeX`).

* **`nodesRefX`** (proved): in the split fragment `MultiImpFrag`, the reference machine finishes
  the instantiation with the host log of the IR's node calls, in a configuration satisfying
  `NodesInv` (the final frame related to the reading, each node's core instance the gap image of
  its IR store after its start function);
* `nodesRef_of_X`: `Task.nodesRef` is its projection;
* `startAdequacyFrag_of_X`: **`Task.startAdequacy` on the fragment from `Task.exportRefX`** (the
  export call from the invariant);
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

end Silmaril.Wasm.Component.DecoderBridge
