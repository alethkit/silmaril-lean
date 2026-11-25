# Varint round trips for widths three through eight in the prepared SQLite reactor

`SqliteWasm.reactorPreparedOrdinaryRoundtrip` composes internal calls
in the pinned, directly prepared reactor. The canonical typed fixture
has 23 function imports. Allocation binds the quoted writer at slot
530 (defined ordinal 507), helper at 547 (ordinal 524), and reader at
434 (ordinal 411). The helper reads global index 0, the mutable i32
stack pointer initialized to 126112. Its scratch starts at 126102.

The theorem takes a width from three through eight and a UInt64 in its
canonical interval `[128^(width-1), 128^width)`. The common i32 address
has eight bytes in bounds. The writer requires its width-sized output
range to be disjoint from its width-sized scratch range. It puts the
reversed encoding in scratch and the encoding at the common address.
`Varint.read?_encode_normal` gives the same value and an offset increase
of the given width in that intermediate memory. The reader writes the
eight little-endian bytes at the common address. That write may overlap
scratch. Both calls return the width as i32 in the original caller
frame. The final store contains the specified three splices in order.

The ordinary import starts from the pinned original bytes through
`originalDecode`. It specializes the lower endpoint at address 126098,
where readback reaches scratch, and the upper endpoint at 131064, the
last fitting eight-byte address. Three bounded kernel replays use a
compact manually linked fixture. They check the three-byte writer's
encoding and scratch bytes, the corresponding reader write that
overwrites scratch, and an eight-byte sequence whose readback is
disjoint from scratch.

## Reproduce

Build the writer and successful-reader fixtures in one generated directory.

```sh
bash tools/sqlite-wasm/check-put-varint.sh ARCHIVE_DIR WORK_DIR
bash tools/sqlite-wasm/check-get-varint.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder commands](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then check the prepared proof and consumer.

```sh
bash tools/sqlite-wasm/prepared-varint-ordinary-roundtrip/check.sh WORK_DIR/lean/SqliteWasm
```

The checker prints the axiom dependencies of the composition and its
original-artifact linkage.
