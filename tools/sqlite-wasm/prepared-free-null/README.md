# Free a null pointer in the prepared SQLite reactor

`SqliteWasm.reactorPreparedFreeNull` resolves the named `free`
export in the canonical directly prepared reactor. Source slot 1546
forwards the argument to the helper linked at slot 1547. With
argument i32 0, the helper takes its null branch and exits before
reading allocator memory.

The theorem establishes `InvokeOk` for i32 0. Core returns no values
with the entire prepared store and the empty invoke frame. The
theorem covers the null pointer in this pinned artifact.

An ordinary import uses `originalDecode` for preparation and the
two quoted function bodies. A packed selector independently checks
the original-byte export. A bounded kernel replay uses a small
manually linked store with memory and global sentinels and compares
the complete final configuration.

## Reproduce

Build the pinned reactor and artifact checks.

```sh
bash tools/sqlite-wasm/check.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder recipe](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Run the standalone checker.

```sh
bash tools/sqlite-wasm/prepared-free-null/check.sh WORK_DIR/lean/SqliteWasm
```
