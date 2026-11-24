# SQLite reactor varint encoder for all UInt64 inputs

[`PutVarint.lean`](PutVarint.lean) exposes `SqliteWasm.putVarint` for
the actual quoted reactor function at index 530. The theorem returns
the length of `Varint.encode` as i32, restores the caller frame, and
specifies the entire final store. The runtime slot and function type
must bind the caller's call to the quoted code.

| Input | Runtime memory and global premises | Exact writes |
| --- | --- | --- |
| Below 16,384 | Wrapper memory 0 has room for the encoding | Output |
| 16,384 through `2^56−1` | Slot 547 binds the quoted helper, whose memory 0 admits the disjoint output and scratch ranges and whose global 0 supplies the i32 stack pointer | Output plus reversed encoding at stack pointer minus 10 |
| `2^56` through `2^64−1` | Slot 547 binds the quoted helper, whose memory 0 has nine bytes in bounds and whose global 0 supplies an i32 value | Output |

The ordinary helper preserves the other state under its stated
nonwrapping and disjoint-range premises. On the nine-byte branch, the
common prologue reads global 0 and subtracts 16 in i32 arithmetic.
The branch uses no scratch address and needs no lower bound on the stack
pointer. It writes the low octet first at effective address `ptr + 8`,
then writes the seven-bit digits at indices seven through zero. The
`ptr + 8 ≤ 2^32` premise refers to the eight loop positions, whose
i32 address arithmetic may use offsets up to seven. The ninth byte
uses Wasm's natural effective-address addition at the immediate offset.
[Nine-byte helper proof](NineByteVarint.lean)

The kernel checks one loop invariant for the nine-byte branch. Local 1
contains the remaining bits after the low-octet store and each subsequent
seven-bit shift. Local 3 counts the descending output index. The memory
is exactly the suffix of the spec encoding already written at its final
offset. Each transition prepends a byte to that suffix. The zero index
produces the full output slice and the next i32 counter value is the exit
sentinel. The proof reuses the Core bridge from the ordinary branch.
[Ordinary helper and Core bridge](OrdinaryVarintHelper.lean)

The downstream consumer distinguishes the wrapper's memory address from
the helper's. It checks both inline paths with the helper absent, the first
ordinary forwarded input, and both endpoints of the nine-byte interval
with stack pointer zero. These cases exercise `MemoryPremises` and the
exact result through ordinary imports.
[Consumer](PutVarintImport.lean)

Run the pinned reactor fixture, earlier proof checks, and these new modules
with the [documented inputs](README.md#reproduce).

```sh
bash tools/sqlite-wasm/check-put-varint.sh "$inputs" .lake/sqlite-wasm-put-varint
```

Add `.lake/sqlite-wasm-put-varint/lean` to `LEAN_PATH`, then import
`SqliteWasm.PutVarint`. The checker prints the axiom audits. The proof
is about a call to the selected code with the given bindings.
[Original-byte records for the two functions](ArtifactCheck.lean)
