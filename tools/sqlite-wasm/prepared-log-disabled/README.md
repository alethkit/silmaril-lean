# Zero-callback logging in the pinned SQLite reactor

`SqliteWasm.reactorLogDisabledCall` follows the actual slot-26 logging
helper with three arbitrary i32 arguments. It uses the pinned function
and allocated signature, the caller's slot and store entry, the mapped
mutable i32 stack global, and a successful four-byte zero read from
address 52996 in the mapped caller memory.

Core subtracts 752 from the stack pointer modulo i32, reads the callback
word, and branches out of the logging block. The epilogue restores the
stack pointer even when subtraction wraps. The call returns no values
to the original caller frame with the exact entire initial store.

`SqliteWasm.reactorPreparedLogDisabled` derives the function, stack-global
and memory mappings in the canonical directly prepared reactor. Its
callback-word premise refers to the exact mapped memory; this result
stops at the zero-callback branch. An ordinary import uses
`originalDecode` and an independent packed Function/Code selector to
link the result to the original Wasm bytes. A manually linked fixture
proves the four-byte read from a zero-filled page using array extraction
laws, then checks the entire Core configuration at return with an
initial stack pointer of 256 and memory, global and caller sentinels.

## Reproduce

Build the pinned reactor and artifact checks.

```sh
bash tools/sqlite-wasm/check.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder recipe](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then run the standalone checker.

```sh
bash tools/sqlite-wasm/prepared-log-disabled/check.sh WORK_DIR/lean/SqliteWasm
```
