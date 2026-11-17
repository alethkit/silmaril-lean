module

public import Silmaril.Wasm.Component.DecoderBridge.Sem.Defs
public import Silmaril.Wasm.Component.InstTestsRef.Thms

/-!
# The two test binaries as instances of the open behavioural goals

`starts_of`, `trap_of`: the reference halves of `InstTestsRef.starts_agree` and `trap_agree`
follow from `Task.startAdequacy` and `Task.failAdequacy` applied to the test binaries: their
hypotheses (both readings succeed, the REF reading is valid, the import is `f: func(u32)`, the
first export is `get`, the IR play) are discharged by the existing theorems, with no new kernel
run. The conclusions are also proved unconditionally, by executing the reference machine
(`InstTestsRef.starts_agree`, `trap_agree`); so the two goals hold on these two binaries.
Neither goal is proved in general.
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

/-- **`starts.wasm` is an instance of `Task.startAdequacy`.** -/
theorem starts_of (h : Task.startAdequacy) :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
        ((), logOfCalls startsTrace)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  h startsBytes startsComp startsRef startsTrace "get" [.u32 42] parse_starts decodeRef_starts
    starts_valid rfl rfl (by simp [startsTrace]) (starts_inst _)

/-- **`trap.wasm` is an instance of `Task.failAdequacy`.** -/
theorem trap_of (h : Task.failAdequacy) :
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX trapRef (importArgs hostI) :=
  h trapBytes trapComp trapRef parse_trap decodeRef_trap trap_valid rfl (trap_inst _)

end Silmaril.Wasm.Component.DecoderBridge
