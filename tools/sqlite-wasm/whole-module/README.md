# Whole-module decode of the pinned SQLite reactor

Import `SqliteWasm.WholeModule` from the generated Lean root.

```lean
SqliteWasm.originalDecode :
  Silmaril.Wasm.Binary.Core.decode? SqliteWasm.originalBytes.toByteArray =
    some SqliteWasm.sqlite
```

This equality covers the complete module returned by Silmaril's ordinary
Core decoder, including all 1,533 defined functions and both Data segments.
The input is the original 741,717-byte stripped linker output, ingested as
`originalBytes`. The output is the ordinary structured quotation `sqlite`.
The downstream import applies the theorem and checks its axiom dependencies
against the repository policy. [Statement](WholeModule.lean) ·
[Downstream regression](ImportCheck.lean) · [Reactor manifest](../reactor.json)

## Composition

Lean checks the original eight header bytes against the Core magic and
version. The packed span scan checks the complete layout. The module loop
uses these exact section boundaries.

| Section | Envelope starts at | Payload interval |
| --- | ---: | --- |
| Type | 8 | `[11, 529)` |
| Import | 529 | `[532, 1450)` |
| Function | 1450 | `[1453, 2988)` |
| Table | 2988 | `[2990, 2997)` |
| Memory | 2997 | `[2999, 3002)` |
| Global | 3002 | `[3004, 3017)` |
| Export | 3017 | `[3020, 3200)` |
| Element | 3200 | `[3203, 3880)` |
| Code | 3880 | `[3884, 683402)` |
| Data | 683402 | `[683406, 741717)` |

The Function and Code vector equations supply the payload reads at their
checked spans. Bounded id and size reads lift these to section steps.
The other eight sections already have step theorems. The ten steps start
from the decoder's empty state, check rank order and exact sizes, and join
at adjacent cursors. At 741717 the ordinary loop takes its EOF branch with
fuel remaining. No custom, Tag, Start, or Data Count section is encountered.
[Composition proof](WholeModuleEvidence.lean) · [Function and Code vectors](../full-vectors/README.md) ·
[Metadata vectors](../metadata-vectors/README.md) · [Small sections](../small-sections/README.md) ·
[Data section](../data-section/README.md)

The Core finalization lemma uses the exact end cursor, the equal lengths
of both projections of the quoted function list, and the no-data-index
theorem for the absent Data Count guard. A list induction shows that
`zipFuncs` reassembles the original quoted functions from those projections.
The remaining fields agree by construction, including the quote's empty
tags and absent start. [Core reader](../../../Silmaril/Wasm/Binary/Core/Decode.lean) ·
[Finalization guard](../data-indices/README.md)

File ingestion and SHA-256 checks run outside Lean. The kernel checks the
decoder equation for the ingested literal against the quoted term, using
the earlier checked byte partitions. The theorem concerns Core decoding.
Validation, linking, instantiation and execution are separate.

## Reproduce

Use the pinned artifact from the reactor build, then build the quotation and
each component in the same generated directory. [Reactor build](../README.md#reproduce)

```sh
wasm=.lake/sqlite-wasm/sqlite3.wasm
quoted=.lake/sqlite-wasm/lean/SqliteWasm
bash tools/sqlite-wasm/quote.sh tools/sqlite-wasm/reactor.json "$wasm" "$quoted"
bash tools/sqlite-wasm/check-function-vectors.sh "$wasm" "$quoted"
bash tools/sqlite-wasm/large-bodies/check.sh "$wasm" "$quoted"
bash tools/sqlite-wasm/full-vectors/check.sh "$quoted"
bash tools/sqlite-wasm/metadata-vectors/check.sh "$wasm" "$quoted"
bash tools/sqlite-wasm/small-sections/check.sh "$quoted"
bash tools/sqlite-wasm/data-section/check.sh "$quoted"
bash tools/sqlite-wasm/data-indices/check.sh "$quoted"
bash tools/sqlite-wasm/whole-module/check.sh "$quoted"
```

With the component proofs built, the final composition and ordinary
import use three Lean invocations, each under one second in the measured
run and with a maximum peak RSS of about 1.95 GiB. The composition reuses
the existing 6 GiB Lean allocator ceiling.
