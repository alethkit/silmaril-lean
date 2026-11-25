# Null database and SQL rejection in the pinned SQLite reactor

`SqliteWasm.reactorPreparedPrepareV2NullRejection` resolves the named
`sqlite3_prepare_v2` export in the canonical directly prepared reactor.
It fixes both the database and SQL arguments to zero, and keeps the
remaining three i32 arguments arbitrary. The allocated wrapper, prepare
helper, database check and logger are linked at module slots 113, 105,
130 and 26. The proof composes the landed prologue, database-check
and zero-callback logger theorems.

The statement-output word must fit in the 131072-byte memory and be
disjoint from the callback word and both diagnostic scratch ranges.
The prepared memory must read zero at the four-byte callback word
at 52996. The scratch bounds and callback separation for the fixed
diagnostic addresses are discharged in the proof.

| Order | Byte address | Little-endian i32 word |
| --- | --- | --- |
| First | `stmtOut` | 0 |
| Second | 126080 | 18995 |
| Third | 126104 | 19917 |
| Fourth | 126100 | 149304 |
| Fifth | 126096 | 12389 |

The final store is precisely the initial store with these five writes
to the mapped memory. The statement-output word remains zero.
Core restores the original stack global, unwinds both call frames,
and returns i32 21 in the empty invoke frame. This covers the
named null-input rejection branch.

The ordinary import uses `originalDecode` to link preparation and all
four bodies to the original Wasm bytes. A separate packed export
selector checks the name and slot. The import instantiates the theorem
with output addresses 65536 and 131068, retaining the callback premise.

## Reproduce

Build the pinned reactor and artifact checks.

```sh
bash tools/sqlite-wasm/check.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder recipe](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then run the standalone checker.

```sh
bash tools/sqlite-wasm/prepared-prepare-v2-null-rejection/check.sh WORK_DIR/lean/SqliteWasm
```
