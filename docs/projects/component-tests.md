# Component tests: instantiation-time behaviour of component binaries

Two real component binaries, assembled by a pinned tool, whose behaviour **at instantiation** is
stated by reusable problem shapes and proved in Lean over the bytes; the reference machine runs a
hand transcription of them, and wasmtime is run on the same bytes as an independent oracle.

## The binaries

`examples/component-tests/{starts,trap}.wat`, assembled by the pinned `wasm-tools` 1.262.0
(`tools/wasm-tools/tests/pins.sh`, SHA-256 checked) with `parse`, `strip --all` (no name
sections) and `validate`. `tools/component-tests/build.sh` reproduces the committed `.wasm` files
byte for byte (`--write` rewrites them). Lean reads them with `include_bytes`
(`Silmaril.Wasm.Component.InstTests.startsBytes`, `trapBytes`).

| binary | size | SHA-256 | content |
|---|---|---|---|
| `starts.wasm` | 256 B | `ff543e05…02665f` | imports `f: func(x: u32)`; core instances, in order: `call1` (start: `f(1)`), `call2` (start: `f(2)`), `glob` (start: a mutable global, initially `0`, set to `42`); exports `get: func() -> u32` (`canon lift` of `glob`'s `get`, which reads the global) |
| `trap.wasm` | 188 B | `1cccda32…649d20` | imports `f`; core instances: `trap` (start: `unreachable`; exports `get` returning `7`), then `call2` (start: `f(2)`); exports `trap`'s `get` |

`f` reaches the core instances through `canon lower`, `get` leaves through `canon lift`, so the
import trace is observed in component values: `f(u32 1)`, answered `()`.

## Semantics and assumptions

* **Path.** `Binary.parseComponent` (the verified parser, then the partial lowering to the
  component IR, `Comp Binary.CoreMod`), then the instantiating denotation `Comp.denI` over
  `Binary.coreModSemI P`: each core module is decoded and run on the Core 3.0 engine at profile
  `P`, its start function **at instantiation** (its import calls are moves of the instantiation
  phase; a trap fails it), and core instances are instantiated in program order; a failure is the
  answer of the whole instantiation and later instances are never started. This is
  `Silmaril.Wasi.Accept.componentBytesSystemCore3I P` before its export phase (`Comp.denX`).
* **Profiles.** Existence statements give a play at **every** profile `P`. Exclusion statements
  are about **every** play at **every deterministic profile** `profile o` (every `GrowOracle o`).
* **Finite plays.** Plays are finite; a start function or export call that never returns makes no
  move. **Divergence is not observed**: an exclusion statement constrains the moves that happen.
  (At `profile o` the start runs of these modules reach their normal forms, but that is not part
  of the statements.)
* **Host.** The host is a function answering each import call; the rows use the typed host
  `unitHost` (`f` answered `()`). The clauses about which import calls happen hold whatever the host
  answers; the clauses about outcomes (`ready`, export answers) assume the host answers as given.
* **No async, resources, streams or futures**: the lowering rejects them.

## Shapes

`Silmaril/Project/Shapes/ComponentTest/{Defs,Thms}.lean`. Each takes the bytes `b`; each states
that `b` lowers to some `c` (`Binary.parseComponent b = .ok c`) and then:

| name | Lean | statement about `c` |
|---|---|---|
| `silmaril.shapes.component.test.instantiates` | `Instantiates b host tr` | `tr` is answered by `host`; at every profile `[inst] ++ tr ++ [ready]` is a play; at every deterministic profile the import calls of every play are a prefix of `tr`'s, and a complete instantiation answered by `host` is exactly `tr` followed by `ready` |
| `silmaril.shapes.component.test.inst_traps` | `InstTraps b host tr` | at every profile `[inst] ++ tr ++ [fail ()]` is a play; at every deterministic profile the import calls of every play are a prefix of `tr`'s, and no play answered by `host` contains `ready` or an export answer |
| `silmaril.shapes.component.test.export_returns_after_inst` | `ExportReturnsAfterInst b host tr q v` | at every profile `[inst] ++ tr ++ [ready, q?, v!]` is a play; at every deterministic profile every answer to `q` in a play answered by `host` is `v` |

Consequences (`Thms`): `Instantiates.unique`, `InstTraps.not_ready`, `InstTraps.no_exports`,
`InstTraps.no_calls` (empty trace: no import call at all), `ExportReturnsAfterInst.denX` (the
answer in the export phase), `ExportReturnsAfterInst.instantiates_play`.

## Rows and theorems

`Silmaril/Project/ComponentTests/{Defs,Thms}.lean`, in the group `silmaril.component_tests`
(under `silmaril.all`). All three are proved (`@[solves]`).

| row | shape | statement |
|---|---|---|
| `silmaril.component_tests.starts.instantiates` | `instantiates` | `starts.wasm`, `unitHost`, trace `[f(u32 1) ↦ (), f(u32 2) ↦ ()]` |
| `silmaril.component_tests.starts.get_after_inst` | `export_returns_after_inst` | `starts.wasm`, that trace, `get()` ↦ `u32 42` |
| `silmaril.component_tests.trap.inst_traps` | `inst_traps` | `trap.wasm`, `unitHost`, empty trace |

They come from `Silmaril.Wasm.Component.InstTests.Thms` (proofs in
`Silmaril/Proofs/Wasm/Component/InstTests/`):

* **Bytes.** `parse_starts`, `parse_trap`: the bytes lower to the literal components
  `startsComp`, `trapComp` (one definitional check by the kernel, `kernel_rfl`); the core decoder
  reads the embedded modules as the litmus modules of `InstLitmus` (`coreModule_*`), so
  `startsComp.denI (coreModSemI P) = startsC.denI (core3SemI P)` (`Transfer`).
* **Existence** (`Pos`): the plays are assembled node by node from Core 3.0 start runs built from
  `Step` rules and instances computed by `decide +kernel` (`InstLitmus`), through the `canon
  lower`/`canon lift` wiring (`lowF_runs`, `getL_runs`).
* **Exclusion** (`Det`): at `profile o` each module is bounded by a script (`callMod_le_script`,
  `trapMod_le_script`, and the new `globMod_le_script`: `inst` → `ready`, `get()` → `42`, by a
  simulation using the uniqueness of normal forms); so the components are bounded by handlers
  whose programs are computed by reduction. Generic handler facts: `handler_ans_pure`,
  `runs_of_instPlay`, `runs_host_unique`, `mem_ofHandler_of_guard`.

`starts_get` gives the component-level uniqueness of the export answer at deterministic profiles,
which `InstLitmus` leaves open for `globC`/`callGlobC` (only the module-level `globMod_get_det`
is there).

`#print axioms` of every answer theorem: `[propext, Classical.choice, Quot.sound]`.

## The reference machine (these two examples only)

`Silmaril.Wasm.Component.InstTestsRef`: `startsRef`, `trapRef` are **hand transcriptions** of the
WAT in the reference machine's syntax (there is no translation from component binaries to it);
their core modules are those decoded from the binaries' bytes. `starts_agree`: the IR play above,
and the reference machine under the logging host instantiates `startsRef` with the host log
`f(1)`, `f(2)` (`logOfCalls startsTrace`) and answers `get()` with `u32 42`. `trap_agree`: the IR
instantiation fails and the reference instantiation traps. The reference side is one executed run
each (`decide +kernel` on `sessSummary` and on a trap summary, then their soundness theorems). No
general adequacy between `Comp.denI` and the reference machine is claimed.

## Oracle: wasmtime (not a proof, not in CI)

`python3 -I tools/component-tests/oracle.py` writes `examples/component-tests/oracle.json`. The
wasmtime CLI cannot supply a host function for a component import (running a binary alone fails
with `component imports function f, but a matching implementation was not found`, recorded as
`alone`). The host is therefore a component, `tools/component-tests/host.wat` (`f(x)` sets
`trace := trace * 10 + x` and counts the calls), composed with the test binary by `wac compose`
(the test binary is embedded verbatim, recorded). `wasmtime run --invoke 'get()'` (then `trace()`,
`calls()`) instantiates the composition afresh each time.

| binary | observed | expected |
|---|---|---|
| `starts.wasm` | instantiates; trace `12` (`f(1)` then `f(2)`), 2 calls; `get()` = `42` | the same |
| `trap.wasm` | every invocation fails at instantiation: `wasm trap: wasm unreachable instruction executed` | whole-instantiation trap |

Provenance in the JSON: wasmtime 50.0.0 (SHA-256 `f95e5beb…00e9b7`), wac 0.12.0 (`7cd490ed…d3beda`),
wasm-tools 1.262.0 (`fe6a056d…18acb211`), the SHA-256 of each binary and composition, the commands
and their outputs.

## Explorer

The rows and shapes appear in the generic problem views. The view `#/component-tests`
(`tools/silmaril-project/src/project/explore/views/component-tests.js`) shows, per binary: the
bytes (download, SHA-256, WAT), imports, exports, core instances, the expected trace and outcome,
the rows with their status, the theorem strength, the reference-machine theorem, the oracle's
observations and verdict, and the assumptions and tool provenance. Data:
`examples/component-tests/{report,oracle}.json`, copied next to the page by `make pages`. Node test:
`tools/silmaril-project/tests/explore/component_tests_view.test.mjs`.

## Not covered

* General adequacy of `Comp.denI` with respect to the reference machine (only these examples).
* Divergence (not observed by the shapes).
* Other import types, several imports, nested components, resources, async.
* A translation from component binaries to the reference syntax (the REF side is a transcription).
