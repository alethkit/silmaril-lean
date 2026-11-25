# Nine-byte varint round trip in the prepared SQLite reactor

`SqliteWasm.reactorPreparedNineByteRoundtrip` composes two internal
calls in the pinned, directly prepared reactor. The canonical typed
fixture has 23 function imports. Allocation binds the writer at slot
530 (defined ordinal 507), its helper at 547 (ordinal 524), and the
reader at 434 (ordinal 411) to their quoted bodies and closed
runtime signatures. The writer helper reads the mutable i32 stack
global at index 0, which preparation sets to 126112.

For a UInt64 value at least 2^56 and a common i32 address with nine
bytes in bounds, the writer's final memory is the nine-byte
`Varint.encode` splice. The bound and prepared memory size imply the
nonwrapping bound for the writer and the eight-byte destination bound
for the reader. The writer contract requires the stack-global lookup
and the output bounds. `Varint.read?_encode_nine` gives the original
value and advances the offset by nine in the intermediate memory.
The reader writes exactly the eight little-endian bytes of the value
over the first eight encoded bytes. The ninth encoded byte remains
at its original position. Both calls return i32 9 in the original
caller frame. The final store is the prepared store with the specified
two splices in the resolved callee memory.

The ordinary import starts from the pinned original bytes through
`originalDecode` and specializes at both endpoints and the last fitting
nine-byte address. Five bounded replays in a compact manually linked
store check both writer-only and combined endpoint calls, plus a
combined call with a nonzero ninth encoded byte. The prepared-state
proof concerns these internal nine-byte paths in the canonical fixture.

## Reproduce

Build the writer and successful-reader fixtures in one generated directory.

```sh
bash tools/sqlite-wasm/check-put-varint.sh ARCHIVE_DIR WORK_DIR
bash tools/sqlite-wasm/check-get-varint.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder commands](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` set to
`WORK_DIR/lean/SqliteWasm`. Then check the prepared proof and consumer.

```sh
bash tools/sqlite-wasm/prepared-varint-nine-byte-roundtrip/check.sh WORK_DIR/lean/SqliteWasm
```

The checker prints the axiom dependencies of the composition and
its original-artifact linkage.
