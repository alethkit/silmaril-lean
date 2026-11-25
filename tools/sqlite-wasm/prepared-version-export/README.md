# Named version invocation in the prepared SQLite reactor

`SqliteWasm.reactorPreparedVersionExport` resolves the pinned
`sqlite3_libversion_number` export in the canonical directly prepared
instance. The source export selects module slot 289. With 23 function
imports, allocation resolves defined ordinal 266 to its actual store
address and closes its `() → i32` signature. The theorem establishes
`InvokeOk` with an empty argument list.

The Core invocation reaches i32 3054001, SQLite's numeric version for
the pinned 3.54.1 release, in the empty invoke frame. The final store
equals the prepared store. The proof uses the existing `version_body`
for the selected code and Core steps for entry and value return.

The ordinary import uses `originalDecode` to apply the theorem to the
pinned original bytes. A bounded kernel replay uses a compact manually
linked store with memory and global sentinels and compares the entire
final configuration.

## Reproduce

Build the pinned source reactor and artifact checks in a generated
directory.

```sh
bash tools/sqlite-wasm/check.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder commands](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then run the prepared version checker.

```sh
bash tools/sqlite-wasm/prepared-version-export/check.sh WORK_DIR/lean/SqliteWasm
```

It rebuilds direct preparation and the existing `VersionModel` and
`VersionCheck` modules, then builds the Core proof and its ordinary
consumer. The checker prints the axiom dependencies.
