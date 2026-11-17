module

public import Silmaril.Wasm.Component.DecoderBridge.Multi.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Sim.Thms
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Compose
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.IR
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.First

/-!
# Several core instantiations with lowered imports: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi`.

* `startAdequacyFrag_of` (proved): **`Task.startAdequacy` on the fragment `MultiImpFrag` from
  its four pieces** `Task.nodeCallsIR` (a), `Task.firstNodeRef` (b), `Task.laterNodesRef` (c) and
  `Task.exportRef` (d);
* `starts_multiImpFrag` (kernel, `decide +kernel`): `starts.wasm` is in the fragment;
* `starts_of_frag`: the reference half of `InstTestsRef.starts_agree`, derived from the IR's run
  of `starts.wasm` (`starts_inst`) through the pieces. The conclusion is also proved
  unconditionally by executing the reference machine (`InstTestsRef.starts_agree`).
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

/-- **The start goal on the fragment, from its four pieces.** -/
theorem startAdequacyFrag_of (ha : Task.nodeCallsIR) (hb : Task.firstNodeRef)
    (hc : Task.laterNodesRef) (hd : Task.exportRef) : Task.startAdequacyFrag :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.startAdequacyFrag_of ha hb hc hd

/-- **Piece (a), the IR's node calls**: in the fragment, a ready node-by-node instantiation with
the calls `t`, each answered `()`, is the nodes' `NodeCalls` with the calls `ts`, `t = ts.flatten`. -/
theorem nodeCallsIR : Task.nodeCallsIR :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.nodeCallsIR

/-- **Piece (b), the first node with its start epilogue**: if the IR's first node is ready after
the calls `t₀`, the reference machine runs the definitions up to and including the first core
instantiation (root checks, trampolines, preparation, the start function with its host calls and
its epilogue), with the host log `logOfCalls t₀`. -/
theorem firstNodeRef : Task.firstNodeRef :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.firstNodeRef

/-- **The start goal on the fragment from the remaining pieces (c) and (d).** -/
theorem startAdequacyFrag_of_cd (hc : Task.laterNodesRef) (hd : Task.exportRef) :
    Task.startAdequacyFrag :=
  startAdequacyFrag_of nodeCallsIR firstNodeRef hc hd

/-- **The start goal on the fragment, from (a), (b'), (c') and (d)**: the pieces with the
finishing continuation (`RefAtDefsK`). -/
theorem startAdequacyFrag_of_K (ha : Task.nodeCallsIR) (hb : Task.firstNodeRefK)
    (hc : Task.laterNodesRefK) (hd : Task.exportRef) : Task.startAdequacyFrag :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.startAdequacyFrag_of_K ha hb hc hd

/-- `starts.wasm` is in the fragment. -/
theorem starts_multiImpFrag : MultiImpFrag startsRef := by decide +kernel

/-- **`starts.wasm` from the IR's run, through the start goal on the fragment.** -/
theorem starts_of_frag (h : Task.startAdequacyFrag) :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
        ((), logOfCalls startsTrace)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  h startsBytes startsComp startsRef startsTrace "get" [.u32 42] parse_starts decodeRef_starts
    starts_valid starts_multiImpFrag rfl rfl (by simp [startsTrace]) (starts_inst _)

/-- **`starts.wasm` from the IR's run, from the remaining pieces (c) and (d).** -/
theorem starts_of_cd (hc : Task.laterNodesRef) (hd : Task.exportRef) :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
        ((), logOfCalls startsTrace)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  starts_of_frag (startAdequacyFrag_of_cd hc hd)

end Silmaril.Wasm.Component.DecoderBridge
