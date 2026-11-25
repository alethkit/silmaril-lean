# Prepared SQLite varint round trips across all encoded widths

`SqliteWasm.reactorPreparedVarintRoundtrip` composes the prepared
one-byte, two-byte, widths-three-through-eight, and nine-byte proofs.
Their `prepareDirect?` and callee memory lookup results supply the
same canonical reactor state. The four proofs establish the actual
writer and reader linkage for that state.

For a UInt64 value and shared i32 address, let the width be
`(Varint.encode value).length`. The address must have room for
`max 8 width` bytes in callee memory. For values from 16384 through
`2^56 - 1`, the width-sized writer output and scratch range starting
at 126102 must be disjoint. In those cases the writer first puts the
reversed encoding in scratch. The encoded-output splice follows,
and the reader applies the exact eight-byte little-endian splice to
the intermediate memory. Readback may overlap scratch. The
functional decode recovers the input value and advances by the
encoded length. Both internal calls return that length as i32 in
the original caller frame. The conclusion gives their exact final
store for the canonical typed fixture.

The ordinary consumer starts from the pinned original bytes via
`originalDecode`. Its finite controls instantiate all eight
threshold endpoints at address 131063, the last fitting nine-byte
start. It also checks the three-byte scratch-overlap case at 126098
and that the nine-byte bound excludes the last eight-byte start.
The quantified theorem composes the four separately verified
prepared paths.

## Reproduce

Build the writer and successful-reader fixtures in one generated directory.

```sh
bash tools/sqlite-wasm/check-put-varint.sh ARCHIVE_DIR WORK_DIR
bash tools/sqlite-wasm/check-get-varint.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder commands](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then build the prepared proof and consumer.

```sh
bash tools/sqlite-wasm/prepared-varint-all-widths-roundtrip/check.sh WORK_DIR/lean/SqliteWasm
```
