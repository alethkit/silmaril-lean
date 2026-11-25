# Two-byte varint round trip in the prepared SQLite reactor

`SqliteWasm.reactorPreparedTwoByteRoundtrip` composes two internal Core
calls in the pinned, directly prepared reactor. Its canonical typed
fixture has 23 function imports. Allocation selects the quoted writer
and reader at module slots 530 and 434, defined ordinals 507 and 411,
with closed signatures `(i32, i64) → i32` and `(i32, i32) → i32`.

For a UInt64 value from 128 through 16383 and a common i32 address
with eight bytes in bounds, the writer splices the two-byte result of
`Varint.encode`. The shared `Varint.read?_encode_two` theorem gives the
original value and the offset advanced by two in the intermediate
memory. The reader uses the same input and destination address and
splices the eight little-endian bytes of the value. Both internal
calls return i32 2 in the original caller frame. The final store
updates the resolved callee memory with exactly the two splices in order.

An ordinary consumer uses `originalDecode` to start from the pinned
original bytes. It instantiates the proof at both value endpoints
and the last address that fits the eight-byte write. Four bounded
kernel replays use a compact manually linked store. They check the
writer alone and the full sequence at both endpoints, with memory
sentinels and the caller frame. The prepared-state result covers the
canonical typed fixture and the internal two-byte paths.

## Reproduce

Build the successful-reader fixture.

```sh
bash tools/sqlite-wasm/check-get-varint.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder commands](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then check the preparation, writer,
composed proof, and ordinary consumer.

```sh
bash tools/sqlite-wasm/prepared-varint-two-byte-roundtrip/check.sh WORK_DIR/lean/SqliteWasm
```

The checker prints the axioms for the composed proof and the
original-artifact linkage.
