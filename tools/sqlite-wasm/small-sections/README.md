# Remaining small sections of the pinned SQLite reactor

The four `SectionRun` theorems equate the original Table, Memory, Global
and Element vectors to `sqlite.tables`, `sqlite.memories`, `sqlite.globals`
and `sqlite.elems`. The proofs use the same `SqliteWasm.originalBytes` as
the earlier Function, Code, Type, Import and Export checks. [Function and Code vectors](../full-vectors/README.md) ·
[Type, Import and Export vectors](../metadata-vectors/README.md)

| Section | Id byte position | Payload interval | Vector entries |
| --- | ---: | ---: | ---: |
| Table (4) | 2988 | `[2990, 2997)` | 1 |
| Memory (5) | 2997 | `[2999, 3002)` | 1 |
| Global (6) | 3002 | `[3004, 3017)` | 2 |
| Element (9) | 3200 | `[3203, 3880)` | 1 |

Import `SqliteWasm.SmallSections` from the generated Lean root. The public
theorems are `originalTableSection`, `originalMemorySection`,
`originalGlobalSection` and `originalElementSection`. Each theorem verifies
its original section location, id and size field, then gives the complete
Core `readSectionBody` equation for any incoming decoder state. Its `body`
field gives the exact end position and updated quotation field. The `step`
lemma gives the corresponding `readModule.go` equation. The ordinary import
test applies every body equation, composes the Table, Memory and Global
steps, and applies the Element step. [Theorems](SmallSections.lean) ·
[Downstream test](ImportCheck.lean)

Build and quote the pinned reactor first. Run the earlier metadata check and
then this check in the same generated directory. The second command reuses
the previously ingested literal and quotation. SHA-256 and byte ingestion
run in the earlier external fixture setup. [Reactor setup](../README.md#reproduce)

```sh
wasm=.lake/sqlite-wasm/sqlite3.wasm
quoted=.lake/sqlite-wasm/lean/SqliteWasm
bash tools/sqlite-wasm/metadata-vectors/check.sh "$wasm" "$quoted"
bash tools/sqlite-wasm/small-sections/check.sh "$quoted"
```

With the earlier fixture modules cached, the small-section check took
27.51 s and peaked at 5.57 GiB RSS in one Lean process. The check uses the
6 GiB Lean allocator limit.

## Remaining whole-decode obligations

The section results account for every present non-Data payload of this
stripped reactor. The 58,311-byte Data section still needs complete segment
and byte-payload equality. A single direct Data-vector reduction hit the
6 GiB kernel allocator cap. A staged proof can check each segment's mode,
initializer and framed payload against the original using packed slices.

The absent Data Count section requires a separate proof that
`codesDataIdxs` is empty. Direct reduction over the full quoted Code vector
also hit the 6 GiB limit. A trial on the largest quoted code group passed
under that limit. The group results can compose by append before applying
the decoder guard. The complete decode still needs header and section-step
composition, the exact final cursor, and assembly into the quotation.
[Core decoder guards](../../../Silmaril/Wasm/Binary/Core/Decode.lean)

These section equations concern decoding. Module validation, linking,
instantiation and execution remain separate claims.
