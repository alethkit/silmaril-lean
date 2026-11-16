# Wasm components: caveat ledger

What the component developments cover today, ordered by how much they block giving meaning to
real component binaries. Each entry gives the evidence and the next step. Status words:
**wired** (implemented and connected to the public acceptor and consequence APIs),
**unwired** (implemented but not connected), **missing**, **assumption** (a modelling choice)
and **gap** (a verification gap).

## Acceptance of component binaries

| item | status | evidence | next step |
|---|---|---|---|
| `accept(list<u8>)` binaries have meaning, imported or exported `accept` | **wired** on the reference machine (REF) | `Silmaril.Wasi.Accept.Ref`: `Accepted`, `refBytesSystem`, `acceptRun_sound`; `Ref/Examples.lean` decodes and validates a real `accept(list<u8>)` binary in the kernel and runs it (`#guard`), recording `"hi!"`; `AcceptedExport` (REF `exportBehaviours`) for `accept: func(list<u8>) -> bool`, with `#guard`ed runs returning `true`/`false` | see the gaps below; the exported form covers components without root imports, one call after instantiation |
| the component IR reads lists, strings, flags, resources | **missing** | `Binary/Lower/Defs.lean`: `defValTy` rejects them; the IR's `ValTy` has no list type | extend the IR's ABI with linear memory, or keep REF as the semantics of such components |
| an interface (game) denotation of REF components whose plays include **host-function calls** | **missing** (the bridge item 1 means) | REF has an *operational* reading of import calls: `Ref.Accepted`/`AcceptedTyped` observe the host function's arguments in machine runs. The *denotational* side is missing: no map from a REF component to a strategy `Strategy (nsig I) (nsig X)` (a WASI world model, `Layout.compModel`'s codomain) in which a call of a host function is a P-move with its lifted arguments. REF→strategy exists only for import-free `Simple` components (`SessionAdequacy`, `SessionStrat` in review); with host imports, finite REF sessions with a host log equal IR session plays for `HLinked2` (`HLinked2.sessAdequacy_full`), and acceptance through a host import follows on sessions (`HLinked2.sessAccepted_iff`), without a strategy built from REF | define `refModel c : L.world.Model` from REF sessions with host calls, and prove adequacy `AcceptedTypedBytes ft prof c w ↔ w ∈ bytesLang (refModel c) acceptFn` |
| tuple-acceptor bridge (REF ↔ IR on the fragment both read) | **partly done**: prerequisites exposed | `tupleHiBytes` is read by both (kernel); REF passes `accept` a record, so the `list<u8>` notion is empty on it and `AcceptedTypedBytes` (through `bytesOf?`, the IR's `bytes?` reading) is needed; the host must be linked at the component's import type (`acceptLinkedProgAt`); the tuple acceptance is **kernel-checked end to end** (`tupleHi_accepts`) | (P2) **closed**: `bytesOf?_toRefVal` (`bytesOf? [toRefVal v] = bytes? v`, `Ref/Bridge/Thms.lean`); (P3) **closed**: `Binary.coreModSem P` (`Param.engineSem` over `Reference.core3P P` on the decoded bytes) and `componentBytesSystemCore3`; inherited caveat: a core module with a start function has no engine instance (`instOf`), so it traps; (P4) **partly done**, on sessions of `HLinked2` components (`Ref/HostSession/Thms.lean`): `HLinked2.sessAccepted_iff` (under `HLinked2.Adequate` and a typed host `HostTyped g`, every profile and component choice profile): some session of typed calls of `l.toRef` on REF, under the logging host of `g`, logs an `accept` call carrying `w` (`bytesOf?`) iff some session play of `l.toComp.den (impSem P)` whose host calls `g` answers has an answered `accept` call carrying `w` (`args1 bytes?`); `HLinked2.sessAcceptedRef_sub`: such `w` are in `posBytesLang` of the IR (plays with any environment answers). Built on #782's `HLinked2.sessAdequacy_full` and on (P2). **The unrestricted equality is not expected**: the IR's environment may answer `accept` with a trap, after which a session resumes from the trap's store, so the IR language over all plays can contain strings that a host which always answers never observes (a module that sets a global before `accept` and clears it after, and calls `accept` differently when the global is set). The intended statement therefore fixes the host on both sides. Remaining for `AcceptedTypedBytes ft prof (decodeRef b) w ↔ …`: (a) plays that stop inside a call (an `accept` followed by divergence) and unfinished calls, which sessions do not observe; (b) the typed environment of `AcceptedTypedBytes` (`Steps` with `TypedEnvLabel`, interleaved invocations, ticks, cancellations, host `acceptLinkedProgAt`) against `HLinked2.sessObs`; (c) `posBytesLang` of `den` against `bytesLang` of `Layout.compModel` (through `atSizes`, `lowerH`, `upH`); (d) bytes: no map from `decodeValid b`/`decodeBinary b` (`Comp CoreMod` under `Binary.coreModSem P`, `Param.engineSem`) to `HLinked2.toRef`/`toComp` (`Comp ImpModule` under `impSem P`, `IsInstance`); (e) start functions (`HLinked2.Adequate` excludes them). No concrete instance on `tupleHiBytes` is proved: it needs (d) |
| REF↔IR adequacy beyond `Simple` | **partly done** | `Reference.Sound` (`SimpleI.sound`, `SimpleI.sound_seqS`: REF→IR with host imports); `HLinkedSession` (`HLinked2.sessAdequacy_full`: finite session adequacy with host calls and a host log, both directions); `Ref/HostSession` (acceptance through a host import on sessions, above) | (P4) items (a)–(e) above |
| `RefSimple.ofRef?` (bytes → `Simple`) linked to the acceptor APIs | **unwired** | `JcoTool.RefSimple` | use it to check the two paths agree on scalar components |
| real Core 3.0 instances for the jco wrapper model (`Jco.Real.realInst`) linked to REF | **unwired** | `Jco.Real.Inst`, `Jco.Wrap` (`wrap_correct` for strings and `list<u8>` exports, relational) | prove that REF runs the `wrap md` component of a real module as `md.spec` |

## Verification gaps

| item | status | evidence | next step |
|---|---|---|---|
| end-to-end runs with linear memory are not kernel-checked | **gap** | evaluating a 64 KiB memory in the kernel exceeds its recursion depth (`decide +kernel` fails); the run is checked by `#guard` and enters proofs only as a hypothesis (`hi_mem_of_runHi`) | kernel-friendly memory representations (the `Wasm.KernelEval` work in review) |
| no proof that a REF component accepts *only* certain bytes | **gap** | `Accepted` is existential; only inclusions are shown | invariants of REF runs (e.g. a component that never calls `accept` accepts nothing) |
| upstream parity suites (wasm-tools, jco, wac, wasmtime) | **gap** | not run by CI (`docs/projects/wasm-components.md`) | run them in a scheduled job |

## Assumptions of `Ref.Accepted` and the typed environment

* **Host.** The host's `accept` is synchronous: it records its arguments and returns no result.
  It is REF's `mk_host_func` pattern. `acceptLinkedProgAt ft` supplies it at type `ft`, and
  REF's import check makes `ft` the component's import type.
* **Untyped environment (`Accepted`, `EnvLabel`): spurious runs.** Invoking an export on
  arguments that do not have its WIT type violates REF's precondition. Usually the machine
  stops with an `internal` fault, but not always: the exported `len == 3` acceptor returns
  `true` on the ill-typed list `[u32 300, u8 1, u8 2]` (`Ref/Typed/Examples.lean`, `#guard`).
* **Typed environment (`AcceptedTyped`, `TypedEnvLabel`), the intended semantics.** The host
  invokes exported functions only on arguments of their WIT type (`Val.HasType`, checked by
  the kernel-reducible `Val.typeCheckList?`), ticks and cancels. `AcceptedTyped → Accepted`,
  and `refTypedBytesSystem ≤ refBytesSystem`. The typed driver refuses ill-typed calls, as the
  tests show. Making the typed notions the default (replacing the untyped `refBytesSystem`) is
  a reviewer decision; both are kept for now.
* **Re-exported `accept`: intended.** A component that re-exports its `accept` import lets a
  typed host call `accept` through it, so it accepts every byte string the host passes. The
  IR reading (`Wasi.Accept.bytesLang`, import calls in plays of the wiring) counts these calls
  too. It is a property of the component's interface, not an ill-typed host (`#guard` test).
* **Validation and engine.** `refBytesSystem` validates at `Features.p2` and runs over the
  executable Core 3.0 engine `core3 neverFail`. `Accepted` itself holds for any core engine
  and any component choice profile.

## Streams, async and jco

Streams, futures, async lifting and lowering, the stream transformer algebra and the jco-style
toolchain are present (`Silmaril.Wasm.Component.Streams`, `Silmaril.Wasm.Jco`,
`Silmaril.Wasm.JcoTool`, the REF runtime `Reference.Runtime.Stream*`). These items are open:

* a concrete stream semantics (`StreamSem`) for generated modules;
* the link between generated or emitted binaries and the transformer models;
* the `DROPPED`-event gap of the `Async` model;
* parts of the jco adaptor against Core 3.0: stores, `memory.copy`, `if`, traps, and
  `latin1+utf16`.

See `docs/projects/wasm-components.md`.
