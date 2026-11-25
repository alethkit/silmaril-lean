# Quoted reactor nine-byte varint reader

`SqliteWasm.getVarint_nineByte` applies to slot 434 of the pinned
SQLite reactor. It requires nine readable input octets in initial callee
memory and continuation bits on the first eight. The ninth octet
contributes all eight bits, with any UInt8 value allowed. The eight-byte
destination must be in bounds and may overlap the input.

Given the explicit runtime slot, instance, code, signature, and memory
bindings, `Varint.read?` returns the eight base-128 digits followed by
the full ninth byte as a UInt64 and advances to `src.toNat + 9`. The
Core call returns i32 9 in the original caller frame. The exact store
is the initial store with the eight-byte little-endian result spliced
into callee memory 0.

The VC generator checks the quoted body, including the unsigned load
with immediate offset eight. The shared tail lemma checks the i64 shift
by eight, OR with the ninth octet, and the `0x8000` correction. This
correction clears the eighth octet's continuation bit before appending
the ninth. The decoder consumer checks the exact slot-434 function
record with `originalDecode` and the original Function/Code selector.
The behavioral theorem takes runtime linkage as a premise.

## Reproduce

```sh
bash tools/sqlite-wasm/check-get-varint-nine-byte.sh ARCHIVE_DIR WORK_DIR
```

The script rebuilds the six- through eight-byte proofs and replays their
ordinary consumers with the expanded reader support. The nine-byte
consumer imports all nine reader proofs and applies the theorem to
`UInt64`'s maximum value. It kernel-replays overlong zero and both
canonical endpoints, 72057594037927936 and 18446744073709551615, with
the destination overlapping the first eight input octets. Each replay
checks the entire final configuration, including the preserved ninth
source byte and original caller frame.

For the decoder binding, build the
[whole-module fixture](whole-module/README.md#reproduce) in the same
work directory and run the ordinary decoder consumer.

```sh
root="$(realpath WORK_DIR)/lean"
cp tools/sqlite-wasm/GetVarintNineByteDecodeImport.lean "$root/SqliteWasm/"
LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}" \
  lake env lean -j1 -s 131072 -DautoImplicit=false -E warning --root="$root" \
  "$root/SqliteWasm/GetVarintNineByteDecodeImport.lean"
```
