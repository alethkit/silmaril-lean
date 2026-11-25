# Varint reads in the directly prepared SQLite reactor

`SqliteWasm.reactorPreparedReader` composes the pinned reactor's ordinary
direct preparation for the canonical typed import fixture with the
successful-read contract. The resulting runtime supplies the callee
memory and the function entry for slot 434. Allocation places defined
ordinal 411 after 23 imported functions, with its exact quoted body,
allocated module instance, and closed `(i32, i32) → i32` signature.
Segment application preserves that function table.

For a successful `Varint.read?` on the prepared memory and an in-bounds
eight-byte destination, the internal Core call reaches the original
caller frame with i32 `next - src.toNat`. The final store is the initial
store with exactly the eight little-endian bytes of `value.toNat`
spliced into the mapped memory. The input and destination may overlap.
The statement supplies the prepared state and its memory mapping as
part of its conclusion.

The ordinary downstream proof uses `originalDecode` to start preparation
from the ordinary Core decoder on the pinned original bytes. The
execution scope is this internal slot and successful reads of the
directly prepared memory for the typed fixture.

## Reproduce

Build the successful-reader fixture.

```sh
bash tools/sqlite-wasm/check-get-varint.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder commands](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` set to
`WORK_DIR/lean/SqliteWasm`, then run the prepared-reader checker.

```sh
bash tools/sqlite-wasm/prepared-varint-reader/check.sh WORK_DIR/lean/SqliteWasm
```

The checker builds direct preparation, the reader theorem, and its
ordinary decoder consumer. It prints the theorem's axiom dependencies.
The preparation premises and memory effects come from the
[direct preparation proof](../direct-preparation/README.md) and the
[successful-read contract](../get-varint.md).
