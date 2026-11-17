module

public import Silmaril.Wasm.Component.InstTestsRef.Defs
public import Silmaril.Wasm.Component.Binary.Lower.SemI.Defs
public import Silmaril.Wasm.SingleThreaded.Interface
public import Silmaril.Wasm.Component.DecoderBridge.Wire.Defs

/-!
# The two readings of a component binary: the behavioural statements still open

`DecoderBridge.Thms` relates the two readings of a binary syntactically (`Rel`: the same core
modules are instantiated in the same order). What is not proved is that the IR's instantiation
semantics `Comp.denI (Binary.coreModSemI P)` of the IR reading and the reference machine's
behaviours on the REF reading agree on every binary. The two goals below state it for the
class of binaries the test binaries belong to, as `Prop`s (no theorem asserts them):

* `Task.failAdequacy`: a binary importing exactly `f: func(u32)` (`InstLitmus.hostI`) whose
  REF reading is valid, and whose IR instantiation fails before any host call, traps on the
  reference machine under the logging host (`InstRef.embL`, `InstTestsRef.hostConfigX`);
* `Task.startAdequacy`: for such a binary **whose REF reading is in the fragment**
  `DecoderBridge.InFrag` (`Wire.Defs`), if the IR instantiation makes the host calls `t`, each
  answered `()`, becomes ready, and the IR's first export answers a call with no arguments with
  the values `ws`, then the reference machine instantiates the REF reading with the host log
  `InstRef.logOfCalls t` (the same calls in the same order), after which the export of that
  name returns `ws`.

The fragment hypothesis of `Task.startAdequacy` was added after the first statement, which had
none: there, the IR's first export may be a function of an **exported instance**, which the IR
reading names `instance#function` and the reference machine does not report as a function
export at all (`DecoderBridge.InstExport`, on a real binary: a demonstrated mismatch of the two
readings, not a disproof). Comparing such exports needs an export-path lookup on the reference
side, which `InstTestsRef.sessRunFrom` does not have; that comparison is not stated here. Within
the fragment, both readings name the same imports, exports, modules and wiring
(`DecoderBridge.relW_of_decode`); the behavioural agreement is what remains open.

Both use the deterministic IR profile `profile neverFail` (memory growth never fails), the
growth oracle of the reference stepper `core3 neverFail`; at other profiles the IR may fail a
`memory.grow` the reference performs. The reference side is existential (some run, first
scheduling oracle), as in `InstTestsRef`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (profile neverFail)

/-- **Open goal**: on binaries importing `f: func(u32)` with a valid REF reading, an IR
instantiation that fails before any host call traps on the reference machine. -/
def Task.failAdequacy : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    c.imports = hostI →
    instPlay (F := sigU) ([] : List (Σ _ : sigU.Op, Option Payload)) (.fail ()) ∈
      c.denI (Binary.coreModSemI (profile neverFail)) →
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI)

/-- **Open goal**: on binaries importing `f: func(u32)` with a valid REF reading in the fragment
`InFrag`, the host calls of a successful IR instantiation, and the answer of its first export to
a call with no arguments, are those of a reference run. -/
def Task.startAdequacy : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (t : List (Σ _ : sigU.Op, Option Payload)) (n : String) (ws : List Silmaril.Wasm.Component.Val),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    InFrag r → c.imports = hostI → (c.exports.map (·.name)).head? = some n → (∀ x ∈ t, x.2 = InstTests.unitV) →
    instPlay (F := sigU) t .ready ++ [askEx (0, .vals []), ansEx (0, .vals []) (some (.vals ws))] ∈
      c.denI (Binary.coreModSemI (profile neverFail)) →
    (([some (ws.map toRefVal)] : List (Option (List Value.Val))), ((), logOfCalls t)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI) [(n, [])]

end Silmaril.Wasm.Component.DecoderBridge
