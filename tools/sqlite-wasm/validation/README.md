# Core validation of the pinned SQLite reactor

`Benchmark.lean` uses the ordinary Core decoder and
`Silmaril.Wasm.Validation.validate?`. The latter assembles the Core
type, import, declaration, local, instruction, initializer, segment and
interface checks. The executable benchmark uses the Core 3.0 model.
The separate `WFeatures` gates in the wasm-tools compatibility layer
select feature profiles and encoding extensions. This benchmark exercises
the ordinary validator on the exact pinned artifact.
[Validator](../../../Silmaril/Wasm/Validation/Check/Validate.lean) ·
[Module checker](../../../Silmaril/Wasm/Validation/Check/Module.lean) ·
[Feature gate](../../../Silmaril/Wasm/Tools/Validate/Defs.lean)

The executable accepted the 741,717-byte reactor on the measured revision
`8503340de5d0d00daf3d6da6ea25317b0c5d00de` with 1,533 defined bodies,
23 imports and 11 exports. The input's SHA-256 is pinned by `reactor.json`.
The benchmark checks the hash before executing. The in-process times exclude
Lean startup and file ingestion. GNU time measures the entire Lean process
for each run, including the parse in the `validate` invocation. Rates use
decimal MB, normalized by the full input artifact size.

| Executable phase | Median phase time | Phase s/MB | Median process wall | Peak RSS |
| --- | ---: | ---: | ---: | ---: |
| Parse only | 1.634 s | 2.20 | 4.14 s | 2,356,124 KiB |
| Validate parsed module | 1.605 s | 2.16 | 5.52 s | 2,363,100 KiB |

A direct kernel equation for `(validate? sqlite).isSome = true` reached
the 6 GiB allocator limit in 23.44 s (31.60 s/MB) at 6,291,524 KiB peak RSS. The
same limit was reached when checking the assembled module with its body
predicate replaced by constant true. This isolates a remaining non-body
evaluation cost in addition to the cost of checking all bodies.

## Kernel theorem slice

Import `SqliteWasm.ReactorValidation` from the generated Lean root. The
checker split `validate_eq_bodyInputs` is an equation for the ordinary
validator. It shows that the preparation produces exactly the context and
ordered signatures used for ordinary validation. The following results
refer to `sqlite`, the very same quotation returned by `originalDecode`.

```lean
SqliteWasm.originalResolvedSignatures :
  (bodyInputs? sqlite).map (fun inputs => inputs.signatures.length) = some 1533

SqliteWasm.originalFirstBodies :
  ∃ inputs, bodyInputs? sqlite = some inputs ∧
    List.Forall₂ (FuncOk inputs.context) (sqlite.funcs.take 32) (inputs.signatures.take 32)

SqliteWasm.originalVersionBody : BodyValidAt sqlite 266
```

`BodyValidAt` pairs the body and resolved signature at the given
defined-function ordinal and proves `FuncOk` for that pair. The 33
checked bodies retain the full reactor context, including the imported
functions, complete defined-function index space, and the ordinary
module sections. The downstream import uses all three results with
`originalDecode`. It audits their axioms and the checker split against
the repository allowlist. A kernel proof of strict validation of the
remaining 1,500 defined bodies and the remaining module guards is open.
[Statements](ReactorValidation.lean) · [Checker equation](ValidationInputs.lean) ·
[Downstream regression](ImportCheck.lean)

## Reproduce

Run the benchmark against the pinned original Wasm. Run the standalone
kernel check against the directory from the whole-module fixture recipe.
The two commands report build and check time separately. SHA-256 and
file ingestion take place externally. All proof claims follow from kernel
checks and existing soundness lemmas.
[Whole-module fixture setup](../whole-module/README.md#reproduce) ·
[Artifact manifest](../reactor.json)

```sh
bash tools/sqlite-wasm/validation/benchmark.sh .lake/sqlite-wasm/sqlite3.wasm
bash tools/sqlite-wasm/validation/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

On a prebuilt decode fixture, the four Lean invocations for the slice
totaled 24.85 s (33.50 s/MB) with maximum peak RSS of 5,595,400 KiB.
The 21.71 s evidence invocation includes all concrete kernel checks.
The validator library took 26.60 s on its first local build from the
existing project cache and 2.15 s on the cached rerun.

The next proof step is to check the final non-body guards independently
and combine small body groups under this prepared context. Direct
reduction of the first 72-body quotation group reached the same cap in
the grouped probe. Reuse of the exact function order and bounded shard
sizes will be checked in the kernel.
