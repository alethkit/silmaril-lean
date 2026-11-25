# Close a null SQLite handle in the prepared reactor

`SqliteWasm.reactorPreparedCloseNull` resolves the actual named
`sqlite3_close` export in the canonical directly prepared reactor.
The source export names slot 295, which forwards the handle and
a zero flag to the function linked at slot 296.

With argument i32 0, the helper takes the null-handle branch.
It temporarily subtracts 16 from the mutable stack global, then
adds 16 back before returning. The theorem derives `InvokeOk`
for the zero argument and proves that Core returns i32 0
(`SQLITE_OK`) with the entire prepared store and the empty invoke
frame. The path is specific to the null handle.

The ordinary import applies the theorem via `originalDecode` and
connects the helper body through the same decoder equation. The
artifact selectors separately check the original-byte export and
wrapper body. A bounded kernel replay uses a
manually linked store with memory and global sentinels and
compares the complete final configuration.

## Reproduce

Build the pinned source reactor and artifact checks.

```sh
bash tools/sqlite-wasm/check.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder recipe](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then build the proof and ordinary import.

```sh
bash tools/sqlite-wasm/prepared-close-null/check.sh WORK_DIR/lean/SqliteWasm
```
