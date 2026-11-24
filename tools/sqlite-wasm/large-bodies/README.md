# Complete Code records for the four large SQLite reactor bodies

The staged reactor vector theorem verifies the Code framing for ordinals 99,
260, 719 and 767. This separate check proves the complete Core `readCode`
result for each of those zero-based defined-function ordinals. It checks the
size, expanded locals and complete instruction tree against the original
bytes and the quotation. [Staged reactor vectors](../README.md#staged-reactor-function-vectors)

## Reproduce

Build and quote the pinned reactor with the reactor fixture.
From the repository root, run the standalone check against the original Wasm
and the generated Lean root. The optional third argument selects concurrent
body checks and defaults to one. Each body has a 6 GiB Lean allocator limit.
[Reactor setup](../README.md#reproduce)

```sh
bash tools/sqlite-wasm/large-bodies/check.sh \
  .lake/sqlite-wasm/sqlite3.wasm .lake/sqlite-wasm/lean/SqliteWasm
```

Import `SqliteWasm.LargeBodies` from the generated Lean root. For example,
`SqliteWasm.originalCode719` has this type.

```lean
ReadsCodeAt original 719 (sqlite.funcs.map functionCode)[719]!
```

`ReadsCodeAt` states that the original Code envelope, count and preceding
size prefixes locate a record, and that the Core `readCode` parser on the
original bytes returns the quoted locals and instruction tree at exactly the
framed end. The other three theorems have the same statement at their
respective ordinals. The downstream check applies all four theorems through
one ordinary import and checks their dependencies against the existing axiom
allowlist. [Downstream check](ImportCheck.lean)

## Provenance and composition

The generator proposes byte cuts and paths into the already quoted function
body. Each instruction run checks a bounded original packed slice. For split
controls, the opcode and block type are checked on their own slices. The
checked child sequence ends at the original terminator. Composing prefixes
requires their byte positions to meet. Each sequence also proves that the
ordered pieces equal its quoted instruction list. The final proof checks the
size and locals prefixes, the Core locals bound and the original record's
ordinal, then lifts the composed expression to `readCode`.
[Generator](Generate.lean) · [Composition lemmas](BodyComposition.lean)

The external setup checks SHA-256 and ingests the artifact bytes. The kernel
checks the result over the imported byte literal. The theorem concerns the
four Code records. The other section contents and full module equality are
outside this check.

## Body-check cost

In a cached run with four concurrent body processes, ordinal 99 was the
slowest at 218 s, and ordinal 260 had the highest peak RSS at 4.18 GiB.
These measurements exclude the original build and quotation.
