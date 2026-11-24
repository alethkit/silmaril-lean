# No-data-index guard for the pinned SQLite reactor

Import `SqliteWasm.DataIndices` from the generated Lean root.

```lean
SqliteWasm.quotedCodeIndicesEmpty :
  Silmaril.Wasm.Binary.Core.codesDataIdxs
    (SqliteWasm.sqlite.funcs.map SqliteWasmArtifact.functionCode) = []
```

This is the guard used by the ordinary Core module reader when Data Count
is absent. It concerns the data indices referenced by Code, independently
of the Data segments present in the artifact. The ordinary downstream
regression combines this result with `originalAllFunctionVectors` to
discharge the guard for the actual original Code-vector read.
[Statement](DataIndices.lean) · [Downstream regression](ImportCheck.lean) ·
[Original vectors](../full-vectors/README.md) ·
[Core guard](../../../Silmaril/Wasm/Binary/Core/Decode.lean)

The generator proposes the existing quotation's 32 function groups from
the pinned reactor. The kernel checks `codesDataIdxs` on every group and
composes the equations using `List.map_append` and `List.flatMap_append`.
The result type checks the proposed concatenation against the actual
definition of `sqlite.funcs`. File ingestion and SHA-256 comparison run
externally. The theorem's only axioms are `propext`, `Classical.choice`
and `Quot.sound`. [Generator](generate-check.py) · [Reactor manifest](../reactor.json)

## Reproduce

Build the original Function and Code vector proof first, then run this
standalone check with the same generated Lean root. [Vector setup](../full-vectors/README.md#reproduce)

```sh
bash tools/sqlite-wasm/data-indices/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

Direct reduction on the full Code vector reached the 6 GiB Lean allocator
limit after 21 s. With the upstream fixture built, the group check took
about 100 s and peaked at 3.46 GiB RSS in one Lean process. The check uses
the same 6 GiB allocator limit as the earlier vector work.

The theorem supplies one finalization guard. Whole-module equality still
requires composing the section reads, establishing the absence of Data Count
in the resulting state, and proving the remaining guards and assembly.
