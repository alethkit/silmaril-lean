# Statement-output initialization in the prepared SQLite reactor

`SqliteWasm.reactorPreparedPrepareV2ClearsOutput` extends the
[named wrapper-entry proof](../prepared-prepare-v2-entry/README.md)
through the first eight instructions of the actual helper at slot 105.
It derives the initial stack global and memory mapping from the same
pinned directly prepared store.

For five arbitrary i32 arguments with `stmtOut.toNat + 4 ≤ 131072`,
Core lowers global slot 0 from 126112 to 126096, records 126096 in
helper local 7, and writes four zero bytes beginning at `stmtOut`.
The complete final store is the initial store with those two updates.
The outer invoke frame remains empty, the wrapper remains suspended,
and the remaining helper code starts at the database-handle check.
The endpoint precedes that check and SQL preparation.

The ordinary import starts from `originalDecode` and checks the named
export against the original bytes. A 15-step kernel replay from a
small manually linked store verifies the two updates, both neighboring
sentinels, the whole frame stack and the exact pending code.

## Reproduce

Build the pinned reactor and artifact checks.

```sh
bash tools/sqlite-wasm/check.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder recipe](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then run the standalone checker.

```sh
bash tools/sqlite-wasm/prepared-prepare-v2-out-param/check.sh WORK_DIR/lean/SqliteWasm
```
