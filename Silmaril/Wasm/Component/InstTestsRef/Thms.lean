module

public import Silmaril.Wasm.Component.InstTestsRef.Defs
public import Silmaril.Wasm.Component.InstTests.Thms
import Silmaril.Proofs.Wasm.Component.InstTestsRef.Ref

/-!
# Component test binaries on the reference machine: agreement on these two examples

All proved; proofs in `Silmaril.Proofs.Wasm.Component.InstTestsRef`. Each theorem pairs the
binary's play under the instantiating IR (`InstTests.Thms`) with an **executed** run of the
reference machine on the hand transcription `startsRef` / `trapRef` (`decide +kernel` on its
executable drivers, then their soundness theorems):

* `starts_agree` (every profile `P` on the IR side): the IR instantiation of the lowered
  `starts.wasm` calls `f(1)`, `f(2)`, is ready, and `get()` answers `42`; the reference machine,
  under the logging host `embL`, instantiates `startsRef` with the host log
  `logOfCalls startsTrace` (the same two calls, in the same order) and its `get()` returns
  `u32 42`;
* `trap_agree` (every profile `P` on the IR side): the IR instantiation of the lowered
  `trap.wasm` fails; the reference machine's instantiation of `trapRef` traps.

**Scope.** These are agreements on two examples, one IR play against one reference run each
(the reference runs use the Core 3.0 stepper of `core3 neverFail` with the first scheduling
oracle). The reference side reads a hand transcription of the WAT, with the core modules decoded
from the binaries' bytes; that the transcription is the binary's component is not proved (there
is no translation from component binaries to the reference syntax). No general theorem
relating `Comp.denI` to the reference machine's instantiation is claimed.
-/

public section

namespace Silmaril.Wasm.Component.InstTestsRef

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.Numerics (Profile)

/-- **`starts`: the IR and the reference machine make the same host calls in the same order, and
answer `get()` with `42`.** -/
theorem starts_agree (P : Profile) :
    instPlay (F := sigU) startsTrace .ready ++ [askEx getV, ansEx getV v42] ∈
        startsComp.denI (Binary.coreModSemI P) ∧
      (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
          ((), logOfCalls startsTrace)) ∈
        LinkedSession.sessRunBehaviours first.prof (Host.ofEmbedder embL) ((), []) startsRef
          hostI [("get", [])] :=
  ⟨starts_inst P, Silmaril.Proofs.Wasm.Component.InstTestsRef.starts_ref⟩

/-- **`trap`: the IR instantiation fails and the reference machine's instantiation traps.** -/
theorem trap_agree (P : Profile) :
    instPlay (F := sigU) ([] : List (Σ _ : sigU.Op, Option Payload)) (.fail ()) ∈
        trapComp.denI (Binary.coreModSemI P) ∧
      InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL)
        (LinkedSession.hostConfig hostI ((), [])) trapRef (importArgs hostI) :=
  ⟨trap_inst P, Silmaril.Proofs.Wasm.Component.InstTestsRef.trap_ref⟩

end Silmaril.Wasm.Component.InstTestsRef
