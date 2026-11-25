# Finalize a null SQLite statement in the prepared reactor

`SqliteWasm.reactorPreparedFinalizeNull` resolves the named
`sqlite3_finalize` export at source slot 111 in the pinned directly
prepared reactor. With argument i32 0, the inner `br_if 0` falls
through. The code sets local 0 to zero and branches out of the outer
block before processing any statement. The epilogue restores the
stack global and returns the zero value.

The theorem establishes `InvokeOk` for the null handle and proves
that Core returns i32 0 (`SQLITE_OK`) with the entire prepared store
and the empty invoke frame.

An ordinary import uses `originalDecode` and checks the export and
function body directly against the pinned original bytes. A bounded
kernel replay compares the complete final configuration in a small
manually linked store with memory and global sentinels.

## Reproduce

Build the pinned reactor and artifact checks.

```sh
bash tools/sqlite-wasm/check.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder recipe](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Run the standalone checker.

```sh
bash tools/sqlite-wasm/prepared-finalize-null/check.sh WORK_DIR/lean/SqliteWasm
```
