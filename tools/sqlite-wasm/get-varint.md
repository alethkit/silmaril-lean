# Successful reads of the quoted SQLite reactor

`SqliteWasm.getVarint_of_read` applies to slot 434 of the pinned SQLite
reactor. Its read premise is
`Varint.read? (File.View.ofBytes ⟨mem.bytes⟩) src.toNat = some (value, next)`
on the initial callee memory. Given explicit runtime function, signature,
and memory bindings and an in-bounds eight-byte destination, the Core
call reaches the original caller frame with an i32 result of
`next - src.toNat`. The exact store is the initial store with
`Memory.encodeLE 8 value.toNat` spliced into the linked callee memory.
The input and destination may overlap.

The proof recovers the readable octets and continuation conditions from
the successful read, then applies the corresponding theorem for widths
one through nine. It checks each branch's natural-number result fits
in UInt64 and uses equality of successful read results to identify the
value and consumed length. The original-byte binding for the same
quoted slot is checked by the
[ordinary decoder consumer](GetVarintNineByteDecodeImport.lean).

## Reproduce

```sh
bash tools/sqlite-wasm/check-get-varint.sh ARCHIVE_DIR WORK_DIR
```

The script builds the nine branch theorems and the successful-read
contract. A downstream Lean module imports the contract and applies it
to overlapping one-, eight-, and nine-byte reads. The nine-byte
fixture decodes 128 from eight continuation octets with zero payload
followed by 0x80. The audit prints the successful-read theorem's
axiom dependencies.
