# Intrinsic certificate for a SQLite reactor constructor call

The pinned reactor decodes to a module with no Start section and an
`_initialize` function export at index 25. The last instruction of that
function calls defined function 23. These facts, including the selection of
function 23 itself, follow from `SqliteWasm.originalDecode`.
[Original decode](../whole-module/README.md) · [Pinned artifact](../reactor.json)

Function 23 has signature `() → ()`, no locals and an empty body. The tool
represents the body as `Intrinsic.Code [] [] []`, checks its erasure against
the selected function, and derives the ordinary `InstrsOk` judgment in any
context with empty locals. This is an intrinsic witness for a function
selected from the original reactor.

`initializerConstructorReturns` gives a four-step Core reduction of a
resolved call to slot 23. Its premises identify the caller slot and store
entry, the selected Wasm function, and the empty runtime signature. It
returns no values with the same store and caller frame, for any numeric
profile and host relation. The reduction uses no memory accesses, global
accesses or host calls. The result covers the constructor call reached
at the end of the exported initializer. The preceding guard, writes and
call to function 1516 require separate execution evidence.

Build the original decoder theorem, then run the targeted check with that
same generated directory. [Decoder setup](../whole-module/README.md#reproduce)

```sh
bash tools/sqlite-wasm/intrinsic-initializer/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

Import `SqliteWasm.IntrinsicInitializer` from the generated Lean root.
The downstream check exercises the public decoder, typing and execution
statements and prints their axiom dependencies. SHA-256 and file ingestion
use the existing fixture setup.
[Theorems](IntrinsicInitializer.lean) · [Downstream check](ImportCheck.lean)
