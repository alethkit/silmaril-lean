# SQLite reactor initializer flag

`originalInitializerFunction` identifies defined function 25 through
`SqliteWasm.originalDecode` for the pinned SQLite reactor. Its body starts
with a guard that reads an i32 at `(global[1] + 59328#32).toNat` in the
current frame's memory 0. The addition uses Wasm i32 arithmetic. The
kernel checks the exact body against this decomposition.
[Original decoder theorem](../whole-module/README.md) · [Artifact pin](../reactor.json)

* `initializerZeroFlag` takes an already-entered initializer body, a resolved
  i32 global and memory, and a successful zero load. It reaches the actual
  remaining instructions, `call 1516; call 23`, with the original frame and
  just the four-byte little-endian write of 1. The successful load proves the
  bound for the write.
* `initializerNonzeroFlag` takes the same mappings and a successful
  nonzero load. The original `unreachable` reduces to a trap with the
  same store and frame, before the write or either call.

These are Core execution paths for an already-entered function body. They
stop before either callee and give no result for a failed load. Ordinary
downstream imports exercise both cases and print the three theorems' axiom
dependencies. The checker reuses the generated file and digest boundary
from the whole-module replay.

After building the [original decoder theorem](../whole-module/README.md#reproduce), run:

```sh
bash tools/sqlite-wasm/initializer-flag/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

The downstream module imports `SqliteWasm.InitializerFlag` from the
generated Lean root. [Statements](InitializerFlag.lean) · [Downstream check](ImportCheck.lean)
