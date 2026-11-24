# Original Data section of the pinned SQLite reactor

Import `SqliteWasm.DataSection` from the generated Lean root.

```lean
SqliteWasm.originalDataSection :
  SqliteWasmArtifact.SectionRun SqliteWasm.original 11 683402 683406 58311
    (fun s => { s with data := SqliteWasm.sqlite.data })
```

The ordinary Core reader updates the Data field for any incoming section
state and finishes at byte 741717. `SectionRun.step` gives the corresponding
module loop step from byte 683402. The ordinary downstream import exercises
both equations and audits the theorem's axioms. [Statement](DataSection.lean) ·
[Downstream regression](ImportCheck.lean)

The section envelope is `[683402, 683406)` and its vector starts with a
one-byte count of 2. Both records are kind 0, active in memory 0.

| Segment | Kind, expression and length prefix | Byte payload | Offset expression |
| --- | --- | --- | --- |
| 0 | `[683407, 683415)` | `[683415, 734785)` (51,370 bytes) | `i32.const 1024` |
| 1 | `[734785, 734793)` | `[734793, 741717)` (6,924 bytes) | `i32.const 52400` |

The Python cuts propose packed payload literals. Lean checks each prefix
and compares **every** payload byte to the corresponding bounded slice of
`SqliteWasm.originalBytes`, using packed integer windows and the
`KBytes.sameBytes` soundness theorem. The two literals also match the byte
arrays in `sqlite.data` by definitional equality. The proof lifts the
prefix reads to absolute cursors, applies the ordinary `readBytes`
extraction law and composes two `readData` runs under the checked vector
count. The section id, size, location and boundary are checked on the
same pinned literal used by the earlier reactor theorems. File ingestion
and SHA-256 comparison happen externally. [Proof](DataSectionEvidence.lean) ·
[Reactor manifest](../reactor.json) · [Other section runs](../small-sections/README.md)

## Reproduce

Build and quote the pinned reactor first. Run the metadata check with this
checkout to build the composition helpers, then run the Data check in the
same generated Lean root. [Reactor setup](../README.md#reproduce)

```sh
wasm=.lake/sqlite-wasm/sqlite3.wasm
quoted=.lake/sqlite-wasm/lean/SqliteWasm
bash tools/sqlite-wasm/metadata-vectors/check.sh "$wasm" "$quoted"
bash tools/sqlite-wasm/data-section/check.sh "$quoted"
```

A direct reduction of the complete Data vector reached the 6 GiB Lean
allocator limit after 26 s. With the upstream fixture built, each of the
three staged Lean invocations took under 1 s, with peak RSS about 1.96 GiB.
A one-byte change to the second payload candidate was rejected by the
kernel comparison.

The result gives one section step of the ordinary decoder. Whole-module
decode equality still requires a Core header equation, composition of all
section runs to the final cursor, the final guards and module assembly.
Validation and instantiation are separate.
