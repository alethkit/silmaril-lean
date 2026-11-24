# Original Type, Import and Export sections of the SQLite reactor

The three theorems compare the complete ordered sections with `sqlite.types`,
`sqlite.imports` and `sqlite.exports` from the pinned reactor quotation. They
use `SqliteWasm.originalBytes`, the packed literal shared with the complete
Function and Code vector theorem. [Reactor manifest](../reactor.json) ·
[Function and Code vectors](../full-vectors/README.md)

Import `SqliteWasm.MetadataVectors` from the generated Lean root. The public
results are `SqliteWasm.originalTypeSection`, `SqliteWasm.originalImportSection`
and `SqliteWasm.originalExportSection`. A `SectionRun` gives the checked
original id and size prefix and a Core `readSectionBody` equation for any
incoming decoder state. The decoder updates the section's field and reaches
its original end. `SectionRun.step` composes this with `readModule.go` at the
original section header under the ordinary order guard. The downstream test
uses all three body equations, composes the Type and Import steps, and uses
the Export step. [Statements](MetadataVectors.lean) · [Downstream test](ImportCheck.lean)

| Section | Id byte position | Payload interval | Entries |
| --- | ---: | --- | ---: |
| Type | 8 | `[11, 529)` | 62 |
| Import | 529 | `[532, 1450)` | 23 |
| Export | 3017 | `[3020, 3200)` | 11 |

The check uses the packed header and section scan to locate each payload, then
checks its id, size and complete Core vector read in bounded slices of the
same literal. The vector reader checks its count and consumes the entire
slice. The framing lemmas lift that read to the original absolute cursor.
SHA-256 and ingestion of the original bytes run in the external fixture setup.
[Concrete checks](VectorEvidence.lean) · [Composition lemmas](SectionRuns.lean)

## Reproduce

Build and quote the pinned reactor first. Run this standalone check from the
repository root. [Reactor setup](../README.md#reproduce)

```sh
bash tools/sqlite-wasm/metadata-vectors/check.sh \
  .lake/sqlite-wasm/sqlite3.wasm .lake/sqlite-wasm/lean/SqliteWasm
```

## Remaining work for whole-reactor decode equality

The packed scan establishes the original header and ordered section spans.
The Function and Code vector theorem gives complete payload reads. The Type,
Import and Export section equations above also supply `readModule.go` steps.
The remaining present section payloads need their own Core results against
`sqlite`. [Core section and module reader](../../../Silmaril/Wasm/Binary/Core/Decode.lean)

| Section | Original payload bytes | Remaining equality |
| --- | ---: | --- |
| Table (4) | 7 | Complete table declarations and their initialization form |
| Memory (5) | 3 | Memory limits and address type |
| Global (6) | 13 | Global types, mutability and initializer expressions |
| Element (9) | 677 | Segment modes, offset and element expressions |
| Data (11) | 58,311 | Segment modes, offset expressions and exact byte payloads |

An external scan locates two kind-0 active data segments for memory 0, with
51,370 and 6,924 payload bytes and constant offsets 1024 and 52400. These are
cut proposals for a later kernel proof. The existing `chkDataVec` and
`go_data` lemmas handle this format. The payload comparison can be staged
with packed byte slices so that it avoids directly reducing a decoder over
the 58 KiB section. [Data checker](../../../Silmaril/Wasm/Component/Chunked/Defs.lean) ·
[Composition interface](../../../Silmaril/Wasm/Component/ChunkedDecode/Thms.lean)

The final proof still needs a Core header read and a single `readModule.go`
run to the exact end. The existing `BodyOf` lemmas can lift the proved
Function and Code reads into steps after checking their two envelopes.
The reactor's stripped section layout has no Tag, Start or Data Count section.
The packed scan assumes this stripped layout. The reactor's `_initialize`
is an export. The assembled state must account for the absent sections'
default fields. The decoder checks
that the Function and Code counts agree and, with no Data Count section, that
`codesDataIdxs` is empty. Data segments may still be present. Assembly must
also relate `zipFuncs` to `sqlite.funcs` and each accumulated field to the
quotation. [Core module assembly](../../../Silmaril/Wasm/Binary/Core/Decode.lean) ·
[Function assembly](../../../Silmaril/Wasm/Binary/Core/Modules.lean)

These are equations for Silmaril's Core binary decoder and its supported
section formats. The decoder checks matters such as UTF-8 names, vector
counts, and declared sizes. Full module equality, index and type validation,
import linking, instantiation and execution behavior are separate claims.
The existing canonical replay is executable evidence. [Replay](../README.md#replay-and-leaf-proof)
