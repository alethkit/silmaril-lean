# One-byte varint round trip in the prepared SQLite reactor

`SqliteWasm.reactorPreparedOneByteRoundtrip` composes two internal Core
calls in the pinned, directly prepared reactor. The canonical typed
fixture has 23 function imports. Direct allocation selects the exact
quoted writer and reader bodies at module slots 530 and 434, defined
ordinals 507 and 411, with the respective closed signatures
`(i32, i64) → i32` and `(i32, i32) → i32`.

For any `UInt64` value below 128 and any i32 address whose eight-byte
range fits the prepared memory, the writer splices the one-byte
`Varint.encode` result at that address. On the resulting memory,
`Varint.read?` returns the original value and advances by one. The
reader uses the same address as input and destination. It splices the
eight little-endian bytes of the decoded value over the encoded octet
and the next seven bytes. The invocation sequence returns two i32
values of 1 in the original caller frame. The final store changes only
the resolved callee memory, by the two specified splices in order.

An ordinary downstream consumer uses `originalDecode` to connect the
prepared state to the pinned original bytes. It instantiates the
theorem at value 127 and the last address that fits the eight-byte
write. Three kernel replays use a compact manually linked store:
the writer alone at 127 and the two calls at 0 and 127. They check the
return values, exact memory bytes, both enclosing sentinels, and
the caller frame. The prepared-state theorem uses relational Core
steps and applies to the canonical typed fixture and one-byte internal
paths.

## Reproduce

Build the successful-reader fixture and use the [whole-module decoder
commands](../whole-module/README.md#reproduce) with `wasm` set to
`WORK_DIR/sqlite3.wasm` and `quoted` to `WORK_DIR/lean/SqliteWasm`.

```sh
bash tools/sqlite-wasm/check-get-varint.sh ARCHIVE_DIR WORK_DIR
bash tools/sqlite-wasm/prepared-varint-roundtrip/check.sh WORK_DIR/lean/SqliteWasm
```

The second command builds direct preparation, the one-byte writer, the
composed proof, and its ordinary consumer. It prints the axioms of
the composed proof and the original-artifact linkage.
