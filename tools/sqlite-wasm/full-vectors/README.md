# Complete Function and Code vectors of the SQLite reactor

`SqliteWasm.originalAllFunctionVectors` is the uniform result for all 1,533
zero-based defined-function ordinals. Import `SqliteWasm.AllFunctionVectors`
from the generated Lean root to use it.

```lean
SqliteWasmArtifact.DecodesAllFunctionVectors SqliteWasm.original SqliteWasm.sqlite.funcs
```

The proposition gives the ordinary Core `readVec readIdx` and
`readVec readCode` results over the original bytes.
Both reads start at their original count prefixes and end at the corresponding
section boundaries. The outputs give every quoted type index, expanded locals
list and instruction tree in order. [Theorem statement](CodeCoverage.lean)

## Reproduce

Build and quote the pinned reactor first. Then run the three checks from the
repository root using the same output directory. The last step reuses the two
upstream proofs and only rechecks Code framing. [Reactor setup](../README.md#reproduce)

```sh
wasm=.lake/sqlite-wasm/sqlite3.wasm
quoted=.lake/sqlite-wasm/lean/SqliteWasm
bash tools/sqlite-wasm/check-function-vectors.sh "$wasm" "$quoted"
bash tools/sqlite-wasm/large-bodies/check.sh "$wasm" "$quoted"
bash tools/sqlite-wasm/full-vectors/check.sh "$quoted"
```

With both proof modules already compiled, the last check took 21.27 s and
peaked at 2.34 GiB RSS in one Lean process.

The frame generator proposes the end of each original size prefix and each
record. Lean reads each size from its original packed slice, verifies that
the records form a consecutive trace, and binds the trace to the Code count
and section boundary. For each covered slot, the success of the staged read
and the original size determine its end cursor. For each framing-only slot,
the bridge matches the trace endpoints with the complete body theorem and
uses that theorem's Core read. The final Code equation uses the ordinary
unmasked vector reader. [Staged vector proof](../README.md#staged-reactor-function-vectors) ·
[Four complete bodies](../large-bodies/README.md) · [Downstream regression](ImportCheck.lean)

SHA-256 and file ingestion take place in the earlier fixture setup outside
the kernel. Section contents outside the Function and Code vectors are
outside this theorem, including type definitions, imports, tables, memories,
globals, exports, elements and data. Module validation, instantiation and
whole-module decode equality remain separate claims.
