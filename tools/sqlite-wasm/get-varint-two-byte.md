# Quoted reactor two-byte varint reader

`SqliteWasm.getVarint_twoByte` applies to function index 434 in the pinned
reactor. In the callee's initial memory, the byte at the unsigned i32 source
address must be at least 128 and the byte at the next effective address
must be below 128. Given the stated runtime function and memory bindings,
and eight destination bytes in bounds, the theorem establishes both results.

- `Varint.read?` returns `first % 128 * 128 + second` as a UInt64 and the
  next offset is the initial offset plus two.
- The Core call returns i32 2 in the original caller frame. Its exact store
  is the initial store with an eight-byte little-endian splice in the
  callee's memory 0. The source bytes may overlap the destination.

The reader consumes overlong two-byte encodings, including `80 00` for zero.
The second load uses immediate offset 1, so its bounds are on the effective
address `src.toNat + 1`. The return count uses i32 arithmetic, in which
`(src + 1) - src + 1` is 2 even if the intermediate addition wraps.

The proof runs the existing VC generator on the actual quoted function,
uses the two signed guards to rule out the other paths under these input
premises, and proves that the surviving shift, xor and mask compute the
Lean value. The checked total call yields the stated Core reachability
result for any profile and host relation. `originalGetVarintFunction`
connects the original Function/Code record to this quote. The linker map
identifies the C symbol for this build. The runtime linkage premises remain
explicit.

From the repository root, with the pinned archives in `ARCHIVE_DIR`:

```sh
bash tools/sqlite-wasm/check-get-varint-two-byte.sh ARCHIVE_DIR WORK_DIR
```

The script rebuilds the quote from the pinned reactor, checks both reader
proofs, and prints their axiom audits. The ordinary downstream import tests
overlong zero and the canonical endpoints 128 and 16383 with overlapping
buffers, distinct caller and callee memory mappings, and sentinels outside
the eight-byte destination.
