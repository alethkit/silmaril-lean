# Entry to the prepare helper in the pinned SQLite reactor

`SqliteWasm.reactorPreparedPrepareV2Entry` resolves the named
`sqlite3_prepare_v2` export in the canonical directly prepared reactor.
It identifies the wrapper (module slot 113, defined ordinal 90) and
its linked helper (slot 105, ordinal 82), and establishes the wrapper's
`InvokeOk` for five arbitrary i32 arguments.

The exact Core configuration at helper entry has the original store
and empty outer invoke frame. The wrapper is suspended around the
helper's new frame. For input `[db, sql, nByte, stmtOut, tailOut]`,
the helper starts with `[db, sql, nByte, 128, 0, stmtOut, tailOut]`
and its declared locals. Its full body is still to execute. The theorem
covers the wrapper calling convention before any SQL preparation or
pointer access.

An ordinary import uses `originalDecode` for preparation and the two
quoted functions. A packed selector also checks the named export
against the pinned original bytes. A compact kernel replay with a
manually linked store verifies that eight interpreter steps reach
the complete helper-entry configuration, including the original
memory and global sentinels.

## Reproduce

Build the pinned reactor and artifact checks.

```sh
bash tools/sqlite-wasm/check.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder recipe](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then run the standalone checker.

```sh
bash tools/sqlite-wasm/prepared-prepare-v2-entry/check.sh WORK_DIR/lean/SqliteWasm
```
