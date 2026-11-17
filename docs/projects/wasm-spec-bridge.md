# The Wasm spec bridge: SpecTec ↔ Core whole-step status

This page records, for Wasm 1.0, 2.0 and 3.0, what is proved between the SpecTec transcription of
the official specification (`WebAssembly/spec@608711107b`, read as in
[spectec/README.md](spectec/README.md)) and the hand-written Core models (`V1.Execution.Step`,
`V2.Execution.Step`, `Execution.Core.Step`). The **SpecTec script is the reference**. The Core
models are not normative, and agreement on tests is not evidence for this bridge. Each claim below
names a Lean theorem, and its assumptions are the ones in that statement.

Direction words:

- **forward**: a Core step implies a SpecTec step between the images. This is *completeness* of the
  Core interpreter: every step the interpreter takes is allowed by the spec.
- **backward**: a SpecTec step from an image implies a Core step to a configuration with that
  image. This is *soundness* of the interpreter: the interpreter can take every step the spec
  allows, and nothing it does is outside the spec, at the configurations the statement covers.
- **equivalence**: both directions at one builtins on one domain.

Reading: unless stated otherwise, SpecTec steps are `Round6.Reading.SStepB env` (the backend
reading of `Step`, i.e. `DDerivesB` with SpecTec's `otherwise`). Builtins are the specification's
host-language primitives (`$ibytes_`, `$growmemory`, …), supplied as `B : Builtins`.

## Bridge matrix

| Version | Forward (Core ⇒ spec) | Backward (spec ⇒ Core) | Equivalence | Open whole-step `Task` |
| --- | --- | --- | --- | --- |
| 1.0 | proved on `Typed10 ∧ Plain10 ∧ GSetOk ∧ MemsAligned10`, `fwdB10` (`wholeStepFwd10`), also in `utf8Env10T` with export names (`stepFwd10U_holds`) | proved on `Typed10 ∧ GoodV1` at `fwdB10` (`wholeStepBwd10B`) and `floatIntB` (`wholeStepBwd10`) | **yes**, `wholeStep10_both` (`fwdB10`, `Typed10 ∧ GoodV1 ∧ Plain10 ∧ MemsAligned10`) | `Utf8Strip10.Task.unstripStep10`, reduced to `Task.unstripStep10Out` (#1015) |
| 2.0 | proved on nested fragments: `Nest20 (FwdStep20GP)` in `simEnv20S (storeB P)` (#1015, widest in the corrected script); scalar stores, bulk memory, `table.fill` nested only in `simEnv20T` (`StoreBulk.fwd_good20B`) | proved on `Typed20 ∧ GoodW` (`wholeStepBwdW`, `floatIntB`; `wholeStepBwdW_growB`) | top-level only: `wholeStepTopVS20` (`growB`, forward on `TopVStep20`, backward on `GoodW`); no nested equivalence | none. `Task.wholeStepBwd` is **refuted** (#1015); `Task.wholeStepValid`, `Task.wholeStepValidS`, `Task.wholeStepBwdV` are refuted |
| 3.0 | proved on `ConfigOk ∧ BoundedSel` (`wholeStepValidR_backend`), on `BoundedSelM ∧ NoMemSimd` (`wholeStepValidRMNoMSH_backend`) | same statements (both halves) | **yes** on those domains (up to `Bwd.ConfigEq` and Core's choice) | `Round7.MemSimd.Task.wholeStepValidRM`, `Round7.Utf8.Task.wholeStepValidRE`, `Task.wholeStepValidREH` (reduced to `BadRules.LeavesREHBwd`, this change) |

Profiles: all whole-step targets are at `Profile.spec nd r` (the spec's nondeterministic NaN and
relaxed choices, with `nd`, `r` universally quantified), except the 2.0 nested forward theorems at
`storeB P` and `laneB`/`growB`, which hold at every profile `P` where stated. Hosts: 1.0 and 2.0
cover host-free stores only (a typed image has no host function: `HostRefute.not_typedV_store_host`,
and the forward half fails at host calls: `HostRefute.not_fwd_host`). 3.0 covers every host with
`HostFinite host ∧ HostOk host` (finitely many outcomes per call; outcomes preserve `StoreOk`,
extend the store and are well typed).

## Wasm 1.0 (`Sim10`)

Encodings: `Sim10.configV hn c`, `Typed10 env hn c` (the image is IL-typed). Builtins
`Whole.fwdB10 nd r = bytesB10 (Profile.spec nd r)`.

Proved:

- `Whole.Task.wholeStepFwd10` (`wholeStepFwd10`, `Proofs/…/Sim10/FwdWhole.lean`):
  ```lean
  ∀ H hn host nd r c c', Typed10 (simEnv10 (fwdB10 nd r)) hn c → Plain10 c.code →
    GSetOk c.store c.frame c.code → MemsAligned10 c.store → Step host c c' →
      Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
        SStepB (simEnv10 (fwdB10 nd r)) (configV hn c) (configV hn c')
  ```
  Runs: `Task.wholeRunFwd10`, `Task.wholeRunFwd10C`, `Task.wholeRunFwd10Inv` (proved).
  `MemsAligned10` cannot be dropped (`not_wholeStepFwd10_unaligned`, `memory.size` over a
  one-byte memory). Stores are covered vacuously: no typed image contains a `STORE` (the
  `STORE` erratum).
- `Whole.Task.wholeStepBwd10B` (`wholeStepBwd10B`, `Proofs/…/Sim10/BwdBoth.lean`):
  ```lean
  ∀ H hn, Function.Injective hn → ∀ host nd r c w,
    Typed10 (simEnv10 (fwdB10 nd r)) hn c → GoodV1 c →
    SStepB (simEnv10 (fwdB10 nd r)) (configV hn c) w → ∃ c', w = configV hn c' ∧ Step host c c'
  ```
  with `GoodV1 c := ResOkL10 … ∧ StoreOk10 c.store ∧ SelOk c.code ∧ GSetOk …`.
  `Sim10.Task.wholeStepBwd10` (the same at `floatIntB`) is proved as `wholeStepBwd10`.
- **Equivalence** `Whole.wholeStep10_both`:
  ```lean
  Function.Injective hn → Typed10 (simEnv10 (fwdB10 nd r)) hn c → GoodV1 c → Plain10 c.code →
    MemsAligned10 c.store →
    (SStepB (simEnv10 (fwdB10 nd r)) (configV hn c) w ↔ ∃ c', w = configV hn c' ∧ Step host c c')
  ```
- `Task.wholeStepNest10` (`wholeStepNest10`): the forward half on `Nest10 Leaf10F` at every
  builtins, given both images typed.
- With non-empty export names (the `$utf8` erratum, `utf8Env10T`): `XSwap.stepFwd10U_holds`,
  `XSwap.wholeRunFwd10U_holds`, from `Utf8Swap10.Task.swapStep10` (`swapStep10_holds`).

Open:

- `Utf8Strip10.Task.unstripStep10` (forward, leg 3 of the export-stripping route):
  ```lean
  ∀ H hn nd r host c c', Typed10 (utf8Env10T (fwdB10 nd r)) hn c → Step host c c' →
    SStepB (utf8Env10T (fwdB10 nd r)) (configV hn (stripConfig10 c)) (configV hn (stripConfig10 c')) →
    SStepB (utf8Env10T (fwdB10 nd r)) (configV hn c) (configV hn c')
  ```
  #1015 proves `unstripStep10_of_out : Task.unstripStep10Out → Task.unstripStep10`
  (and the converse), where `Task.unstripStep10Out` adds
  `¬ (Plain10 c.code ∧ GSetOk c.store c.frame c.code ∧ MemsAligned10 c.store)`; inside the
  invariants the statement is `XSwap.unstripStep10_inv`. No consumer depends on the open leg:
  the forward theorem it was meant for is proved directly (`stepFwd10U_holds`).

## Wasm 2.0 (`Sim20`)

Encodings: `Sim20.configV hn c`, `Typed20 env hn c`. Scripts: `simEnv20 B` (the fixed script),
`simEnv20S B` (the corrected script with `Step/ctxt-instrs`, which the 2.0 script lacks: V2's
documented deviation 1), `simEnv20T B` (with the `STORE` erratum repaired), `simEnv20V`/vector
routes. `WholePages s`: every memory is a whole number of pages.

Refuted targets:

- `Sim20.Task.wholeStepValid` (`Whole.not_wholeStepValid`): `NOP NOP` has no step in the script
  without `ctxt-instrs`.
- `Sim20.Task.wholeStepBwdV` (`not_wholeStepBwdV`): `vtestop-false` fires at every `all_true`
  at scalar builtins.
- `StepFix.Task.wholeStepValidS` (`not_wholeStepValidS`).
- **`Sim20.Task.wholeStepBwd`** (#1015, `Whole.not_wholeStepBwd`):
  ```lean
  ¬ ∀ H hn, Function.Injective hn → ∀ host nd r, ∃ B, ∀ c w, Typed20 (simEnv20 B) hn c →
      SStepB (simEnv20 B) (configV hn c) w → ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c'
  ```
  `Step/memory.grow-fail` has no premise, so at *every* builtins it fires at
  `i32.const 0; memory.grow` with no memory, where V2 is stuck. (Before, only
  `not_wholeStepBwd_noRes`, at `floatIntB`.)

Proved backward (soundness):

- `Sim20.Task.wholeStepBwdW` (`wholeStepBwdW`):
  ```lean
  ∀ H hn, Function.Injective hn → ∀ host nd r c w,
    Typed20 (simEnv20 (floatIntB (Profile.spec nd r))) hn c → CvtOkL c.code → NoVecL c.code →
    ResOkL c.store c.frame c.code →
    SStepB (simEnv20 (floatIntB (Profile.spec nd r))) (configV hn c) w →
    ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c'
  ```
  and `wholeStepBwdW_growB` (the same at `growB`, under `GoodW c := CvtOkL ∧ NoVecL ∧ ResOkL`).
  Exclusions: vector operators (`vecOp20`), conversions V2 leaves undefined, missing resources.
  No backward result exists at `storeB`/`laneB`/`vbytesB` (`InertEnv` fails there), nor in
  `simEnv20S`.

Proved forward (completeness), widest first:

- **`Whole.Task.wholeStepFwd20GP`** (#1015, `wholeStepFwd20GP`):
  ```lean
  ∀ H hn P c c', Typed20 (simEnv20 (storeB P)) hn c → WholePages c.store →
    Nest20 (FwdStep20GP P) c c' →
    Typed20 (simEnv20 (storeB P)) hn c' ∧ SStepB (simEnv20S (storeB P)) (configV hn c) (configV hn c')
  ```
  `FwdStep20GP P := CallIndGood.FwdStep20G P ∨ GoodMerge.LoadPackFwd20`, built from the
  per-family bases by `FwdBase20.or` and the generic context lemma `fwd_nest20`. It contains
  `Task.wholeStepFwd20S`'s fragment (`nest20_fwdGP_of_fwdL`).
- The chain below it, all proved, each nested and in `simEnv20S`:
  `wholeStepFwd20` (`FwdStep20` = `TopVStep20` | `PureFwd20` | `ReadFwd20`, `growB`) ⊂
  `wholeStepFwd20B` (+ `PureFwd20B`, `CallFwd20`) ⊂ `wholeStepFwd20L`/`wholeStepFwd20S`
  (+ `v128.store`, `v128.store_lane`; `laneB`/`storeB`) ⊂ `wholeStepFwd20BL` (+ `block`, `loop`)
  ⊂ `wholeStepFwd20C` (+ `CALL_ADDR`) ⊂ `wholeStepFwd20D` (+ unpacked loads) ⊂
  `wholeStepFwd20E`/`wholeStepFwd20F` (+ `call_indirect`, its trap) ⊂ `FwdStep20G`
  (+ `table.size`, `memory.size`, `table.get`; `CallIndGood.fwd_good20CI`) ⊂ `FwdStep20GP`.
  Side branch: `wholeStepFwd20V` (`vbytesB`).
- Top-level with the backward half at `growB` (`simEnv20`): `wholeStepGrow20`, `wholeStepTop20`,
  `wholeStepTopVar20`, `wholeStepTopVS20`; the nested top fragment `wholeStepNest20`;
  `wholeStepCtxS20`, `wholeStepCtxS20'` (one `ctxt-instrs` frame in `simEnv20S`);
  `wholeStepStoreTop20` (top-level scalar stores, `storeB`, `simEnv20S`).
- In `simEnv20T` (the `STORE` erratum repaired): `StoreBulk.fwd_good20B`, `StoreDeep.fwd_good20D`,
  `GoodMerge.fwd_good20M`: scalar stores at every depth, `memory.fill`, packed loads, along runs.
- With non-empty export names: `Utf8Mono.Task.fwdU20` (`fwdU20_holds`), `Task.unstripStep20`
  (`unstripStep20_holds`), from `Task.swapStep20` (`swapStep20_holds`).

Uncovered V2 constructors in the widest nested `simEnv20S` theorem (`Nest20 FwdStep20GP`):

- `Step`: `storeIntTrap/Val`, `storeFloatTrap/Val`, `storePackTrap/Val` are top-level only there
  (`StoreTop20`): `Typed20 (simEnv20 B)` never holds for code holding a scalar store
  (`not_typedV_instrStore20`) and `simEnv20S` is stuck under `ctxt-instrs` once the store holds a
  storing function (`stuck_configV_storeFn20S`); they are nested in `simEnv20T`.
  `callAddrHost`, `callAddrHostDiv`: the forward half is false there (`not_fwd_host`).
- `PureStep`: all 27 vector operators (covered only by the separate vector route, `simEnv20V`);
  `intUnOp` with an invalid operator and `cvtOp`/`cvtOpTrap` where V2 has no shared conversion
  (`PureRest20N`); `intUnOpTrap`, `floatUnOpTrap`, `floatBinOpTrap` (vacuous in V2).
- `ReadStep`: `tableFill*`, `tableCopy*`, `tableInit*`, `memoryFill*`, `memoryCopy*`,
  `memoryInit*` (only `memory.fill` is nested, in `simEnv20T`; the others have single-step
  witnesses `StoreBulkWit`), `vecLoadOob/Val`, `vecLoadLaneOob/Val` (nowhere).

## Wasm 3.0 (`Sim`, Core 3.0)

Encodings `configV hn c` (and `configVD`, which encodes memory SIMD instructions against IL
`instr`). Domain predicates: `ConfigOk c ts` (Core typing of the configuration);
`Round4.Bounded` (SpecTec's size bounds; its `instrBnd` excludes `vecLoad`, `vecLoadLane`,
`vecStore`, `vecStoreLane`); `NoExports` (every module instance has `exports = []`); `NoMissel`
(no `SimdTy.FloatMissel` instruction: the float SIMD operators, such as `f32x4.sqrt`, that the
evaluator's instance selection leaves untyped);
`BoundedSel c := (Bounded c ∧ NoExports c) ∧ NoMissel c`; `BoundedSelM` admits memory SIMD
(`instrBndM`); `BoundedSelE` replaces `NoExports` by `NamesBnd` (exports within SpecTec's
name bound). Both halves match successors up to `Bwd.ConfigEq` (same store and frame, code
equal up to `CALL_REF` annotations), and the forward half up to Core's choice
(`((∀ c₃, Step c c₃ → c₃ = c') → c'' = c')`).

Refuted rounds: `Task.wholeStep` (`not_wholeStep`), `Integrate.Task.wholeStepBounded`,
`Bwd.Task.wholeStepUpTo`, `Round4.Task.wholeStepValid`, `Round5.Task.wholeStepValidOk`,
`Round5.Task.wholeStepValidSel`, `Round6.Task.wholeStepValidR Target.declarative`.

Proved (both directions):

- `Round6.Task.wholeStepValidR Int.backend` (`wholeStepValidR_backend`):
  ```lean
  ∀ H hn, Function.Injective hn → ∀ host, HostFinite host → HostOk host → ∀ nd r, ∃ B,
    (∀ c c' ts, ConfigOk c ts → BoundedSel c → (∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSel c₁) →
      Step (Profile.spec nd r) host c c' →
      ∃ c'', Step … c c'' ∧ ((∀ c₃, Step … c c₃ → c₃ = c') → c'' = c') ∧
        ∃ d', Bwd.ConfigEq c'' d' ∧ Int.backend.step B (configV hn c) (configV hn d')) ∧
    (∀ c ts w, ConfigOk c ts → BoundedSel c → Int.backend.step B (configV hn c) w →
      ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c')
  ```
- `MSPres.wholeStepValidRMNoMSH_backend : WholeStepValidRMNoMSH`: the same shape on
  `BoundedSelM ∧ NoMemSimd` sources, encoded by `configVD`, for hosts with
  `HostKeepsMS host` (hosts add no memory SIMD code).
- `Round7.Task.wholeStepValidREI` (`wholeStepValidREI_holds`): `wholeStepValidRE` with
  `HostExportBlind`, `HostExportParam` and `StripInj c` (no two module instances differ only in
  exports) added.

Open (frozen):

- `Round7.MemSimd.Task.wholeStepValidRM`: `wholeStepValidR` on `BoundedSelM` (memory SIMD
  admitted), via `configVD`. Strongest reduction: `RMElse.wholeStepValidRM_of_restDPM` from
  `OpenRMRestDPM hn (Profile.spec nd r) host` with fields `forward` (non-cast, non-`EasyP`
  sources, excluding `HCtx.CallCtxStep`), `castsFwd`, `castsBwd` (cast redexes `ref.test`,
  `ref.cast`, `br_on_cast`, `br_on_cast_fail` at non-`EasyP` sources). No per-rule obligation is
  left (`RMAtom`, `RMPure`, `RMRead`, `RMCall`, `RMElse`); the open part is configurations that
  hold or produce memory SIMD code. `HCasts.castsFwdD_noMS`/`castsBwdD_noMS` cover the casts only
  on the `EasyP` side.
- `Round7.Utf8.Task.wholeStepValidRE` (modules may export names, any finite `HostOk` host) and
  `Task.wholeStepValidREH` (the same for export-blind hosts). Reductions:
  `CoreStrip.wholeStepValidRE_of_leaves : LeavesRE → Task.wholeStepValidRE` and
  `wholeStepValidREH_of_leaves : LeavesREH → Task.wholeStepValidREH`, each leaf being
  `EraseFwdAt ∧ EraseBwdAt ∧ ExactAt` per configuration. **The forward leaf is proved for
  export-blind hosts** (this change): `BadRules.badFwdN_BI` proves `BadN.BadFwdN` at round 4's
  primitives, and `BadRules.eraseFwdAt_blind` gives `EraseFwdAt` at every configuration (see
  below). So REH is reduced to the backward and export leaves:
  `BadRules.wholeStepValidREH_of_bwd : LeavesREHBwd → Task.wholeStepValidREH`.
  `EraseBwdAt` and `ExactAt` are proved only at export-free configurations
  (`leavesAt_stripped`) or under `StripInj` and `HostModsSub` (`exactAt_of_REM`). For RE (any
  host) the forward leaf is still open: `badFwdN_BI` needs `HostExportBlind` at the
  `$hostcall` rules, and RE's leaf is stated with `stripHostAt host c.store`.

Nothing in the repository proves `OpenRMRestDPM`, `EraseBwdAt` or `ExactAt` in general, so none
of the three open 3.0 targets closes by composition.

### The forward leaf of REH (this change, `Round9.BadRules`)

`BadN.BadFwdN env` asks that each of the seven rules of `Step`/`Step_read` failing the three
syntactic checks go to the erased side (`Swap.eraseV`) wherever it fires under SpecTec's
`otherwise`. Each fails only because it calls a definition the evaluator-level erasure leaves out
(`EraseAll.excluded`). Proved rule by rule, each composed with round 8's route-2 machinery by
`ruleFwdX` (`BadN.ruleFwdN` with the special conclusion or premise supplied); the shapes are kernel
checks (`decide +kernel`) on the fixed script:

| Rules | Excluded call | Lemma | Assumptions |
| --- | --- | --- | --- |
| `block`, `loop`, `try_table` | `$blocktype_` in `if $blocktype_(z, bt) = R` | `ruleFwd_block` (`applies_blocktype_erase`, `btShape_fixed`) | none |
| `table.grow-succeed`, `memory.grow-succeed` | `$with_tableinst`/`$with_meminst` in the conclusion | `ruleFwd_grow` (`withInstBody_erase`, `callW_erase`, `growShapeN_fixed`) | none |
| `call_ref-hostfunc-res`, `call_ref-hostfunc-div` | `$hostcall` in `if pat <- $hostcall(…)` | `ruleFwd_host` (`hostPrem_fwd`, `hostShapeN_fixed`) | `Function.Injective hn`, `HostFinite host`, `HostExportBlind host` |

Results (namespace `Silmaril.Wasm.SpecTec.Sim.Round9.BadRules`, header
`Silmaril/Wasm/SpecTec/Sim/Round9/BadRules/Thms.lean`):

```lean
theorem badFwdN_of_rules {B : Builtins} (h : ∀ nm ∈ badNames, RuleFwdNm (utf8Env B) nm) :
    BadN.BadFwdN (utf8Env B)
theorem badFwdN_BI (P : Profile) {hn : H → String} {host : HostSemantics H}
    (hinj : Function.Injective hn) (hf : HostFinite host) (hb : HostExportBlind host) :
    BadN.BadFwdN (NxPrims.envBI P hn host)
theorem eraseFwdAt_blind (P : Profile) {hn : H → String} {host : HostSemantics H}
    (hinj : Function.Injective hn) (hf : HostFinite host) (hb : HostExportBlind host)
    (c : Config H) : CoreStrip.EraseFwdAt hn P host c
theorem leavesREH_of_bwd (h : LeavesREHBwd) : CoreStrip.LeavesREH
theorem wholeStepValidREH_of_bwd (h : LeavesREHBwd) : Round7.Task.wholeStepValidREH
```

`RuleFwdNm env nm` is `BadFwdN` at the rules named `nm` (without the hypothesis that they fail
the checks). The remaining REH obligation, `LeavesREHBwd` (`BadRules/Defs.lean`), is
`CoreStrip.LeavesREH` without the forward leaf:

```lean
def LeavesREHBwd : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → Round7.HostExportBlind host →
      ∀ (nd : Bool) (r : RelaxedChoice) (c : Config H) (ts : List CValType),
        ConfigOk c ts → BoundedSelE c →
        CoreStrip.EraseBwdAt hn (Profile.spec nd r) host c ∧
          CoreStrip.ExactAt hn (Profile.spec nd r) host c
```

`EraseBwdAt` (backward: a round-6 step from the stripped image lifts to a round-7 step from the
image, up to erasure) and `ExactAt` (export lists) are not attacked here; route 2 has no backward
derivation transfer outside `otherwise` (`ElseBwd`), so `EraseBwdAt` beyond export-free
configurations needs a backward copy of `NxErase.nAt` and of the seven rule lemmas above.

## Changes in #1015

| Before | After |
| --- | --- |
| `Sim20.Task.wholeStepBwd` frozen, open | refuted: `Whole.not_wholeStepBwd : ¬ Task.wholeStepBwd` |
| widest nested `simEnv20S` forward fragment `FwdStep20G` (no `Task`), packed loads nested only in `simEnv20T` | `Whole.wholeStepFwd20GP : Task.wholeStepFwd20GP` on `Nest20 (FwdStep20G ∨ LoadPackFwd20)` at `storeB P`, every profile |
| `Utf8Strip10.Task.unstripStep10` open on all `Typed10` sources | open only outside `Plain10 ∧ GSetOk ∧ MemsAligned10`: `unstripStep10_of_out : Task.unstripStep10Out → Task.unstripStep10` |

Modules: `Silmaril/Proofs/Wasm/SpecTec/Sim20/Bridge.lean` (header
`Silmaril/Wasm/SpecTec/Sim20/Bridge/Thms.lean`) and
`Silmaril/Proofs/Wasm/SpecTec/Sim10/Bridge10.lean` (header
`Silmaril/Wasm/SpecTec/Sim10/Bridge10/Thms.lean`).

## Changes in this pull request (stacked on #1015)

| Before | After |
| --- | --- |
| `BadN.BadFwdN` (7 rules) open; `REFwd.eraseFwdAt_of_blindN` conditional on it | proved for injective `hn` and finite, export-blind hosts: `BadRules.badFwdN_BI` |
| REH reduced to `LeavesREH` (`EraseFwdAt ∧ EraseBwdAt ∧ ExactAt`) | `EraseFwdAt` proved at every configuration (`eraseFwdAt_blind`); REH reduced to `LeavesREHBwd` (`EraseBwdAt ∧ ExactAt`): `wholeStepValidREH_of_bwd` |

Modules: `Silmaril/Wasm/SpecTec/Sim/Round9/BadRules/{Defs,Thms}.lean` and
`Silmaril/Proofs/Wasm/SpecTec/Sim/Round9/BadRules/{Names,Rule,Blocktype,BlockRules,GrowRules,HostRules,Assemble}.lean`.
