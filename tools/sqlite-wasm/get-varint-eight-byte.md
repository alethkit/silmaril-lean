# Quoted reactor eight-byte varint reader

`SqliteWasm.getVarint_eightByte` applies to slot 434 of the pinned
SQLite reactor. It requires eight readable input octets in the initial
callee memory, with seven continuation bits set and a terminal eighth
octet. The eight-byte output span must be in bounds and may overlap the
input, including when both spans have the same address.

Given the explicit runtime slot, instance, code, signature, and memory
bindings, `Varint.read?` returns the eight base-128 digits as a UInt64
and advances to `src.toNat + 8`. The Core call returns i32 8 in the
original caller frame. Its exact store is the initial store with the
eight-byte little-endian result spliced into callee memory 0.

The VC generator checks the quoted body, including the signed load at
offset seven and the fourth `0x4000` correction. The arithmetic and
Core call transfer reuse the existing Wasm reader support. The decoder
consumer checks the exact slot-434 function record against
`originalDecode` and the original-byte Function/Code selector. The
behavioral theorem concerns the eight-byte branch and takes runtime
linkage as a premise.

## Reproduce

```sh
bash tools/sqlite-wasm/check-get-varint-eight-byte.sh ARCHIVE_DIR WORK_DIR
```

The ordinary consumer imports all eight reader proofs and applies the
theorem at 72057594037927935. It kernel-replays that value, the canonical
minimum 562949953421312, and overlong zero, with the input and output
spans identical in all three cases. Each replay checks the entire final
store, the return, and the caller frame.

For the decoder binding, build the
[whole-module fixture](whole-module/README.md#reproduce) in the same
work directory and run the ordinary decoder consumer.

```sh
root="$(realpath WORK_DIR)/lean"
cp tools/sqlite-wasm/GetVarintEightByteDecodeImport.lean "$root/SqliteWasm/"
LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}" \
  lake env lean -j1 -s 131072 -DautoImplicit=false -E warning --root="$root" \
  "$root/SqliteWasm/GetVarintEightByteDecodeImport.lean"
```
