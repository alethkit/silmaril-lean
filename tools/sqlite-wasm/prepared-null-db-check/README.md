# Null database argument in the pinned SQLite check helper

`SqliteWasm.reactorNullDbCheck` follows the actual slot-130 helper
(defined ordinal 107) for argument i32 zero. It uses the pinned code
and signatures for slots 130 and 26, their linked store entries, the
mapped mutable i32 stack global and the mapped memory.

The helper takes its null branch and writes the four little-endian
bytes of 18995 at `(stackPointer - 16).toNat`, with subtraction modulo
i32. The theorem requires a four-byte bound at that scratch address
and a zero callback word at 52996 disjoint from the write. It uses
the [disabled logger theorem](../prepared-log-disabled/README.md) after
showing that the scratch write preserves the callback word. The helper
restores the original caller and stack value and returns i32 zero.
The final store is the initial store with exactly that scratch write.

An ordinary import checks the original Function/Code selector
and uses `originalDecode` to link both bodies to the original
Wasm bytes. Two manually linked proof fixtures check the exact
bytes `33 4a 00 00` with scratch on either side of the callback word,
including a scratch address immediately after that word. The
theorem covers this internal helper path.

## Reproduce

Build the pinned reactor and artifact checks.

```sh
bash tools/sqlite-wasm/check.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder recipe](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then run the standalone checker.

```sh
bash tools/sqlite-wasm/prepared-null-db-check/check.sh WORK_DIR/lean/SqliteWasm
```
