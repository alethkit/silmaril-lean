# Read a one-byte varint after preparing and initializing the SQLite reactor

`SqliteWasm.reactorPostInitVarint` first invokes the named
`_initialize` export in the canonical directly prepared reactor.
It takes no arguments and returns no values in the empty invoke
frame. The initializer returns the exact store obtained by installing
`threadSetupMemory (initializerMark mem 0) 0` at the mapped address.

In that store, slot 434 still resolves to the allocated instance of
the quoted reader. The callee's memory lookup resolves to the updated
memory, which is 131072 bytes. The marker at byte 59328 gives
`Varint.read? = some (1, 59329)` in that memory.

For any destination with eight bytes in bounds, the internal call
returns i32 1 in the original caller frame and writes the eight
little-endian bytes for 1 to that destination. The exact final store
is the initialized store with that memory splice. The result includes
the overlapping case where the destination is also 59328.

The ordinary consumer rewrites the preparation and function selection
against `originalDecode`. The theorem uses existing Core initialization,
allocation, and one-byte reader proofs.

## Reproduce

Build the pinned source reactor and artifact checks.

```sh
bash tools/sqlite-wasm/check.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder recipe](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then run the standalone proof checker.

```sh
bash tools/sqlite-wasm/post-init-varint/check.sh WORK_DIR/lean/SqliteWasm
```
