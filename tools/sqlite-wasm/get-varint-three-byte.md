# Quoted reactor three-byte varint reader

`SqliteWasm.getVarint_threeByte` covers the three-byte branch of
`sqlite3GetVarint` at function slot 434 in the pinned reactor. The two initial
bytes at effective offsets zero and one are at least 128. The byte at offset
two is below 128. All three lookups use the initial callee memory.

Under the stated function instance, runtime type, and callee memory bindings,
with eight destination bytes in bounds, the theorem establishes both results.

- `Varint.read?` returns the UInt64
  `((first % 128) * 128 + second % 128) * 128 + third` and advances by three.
- The Core call reaches i32 3 in the original caller frame. Its exact store
  is the initial store with an eight-byte little-endian splice into callee
  memory 0. The write may overlap any of the three input bytes.

The existing VC generator checks the quoted function under the three byte
tests. The word proof distributes the two shifts over XOR and moves the
`0x204000` correction to the continuation bits of the first two octets.
The remaining shifts and XORs append disjoint seven-bit digits. The reader
computes its return count as `(src + 2) - src + 1` in i32 arithmetic. The
loads use immediate offsets, so in-bounds byte lookups suffice for the
source span. The theorem includes overlong three-byte encodings.

The kernel equation `originalGetVarintFunction` links slot 434 to the
original Function/Code record. The runtime instance bindings are
premises. This proof imports the existing functional specification
directly from `Silmaril.Formats.Sqlite.Varint.Defs`.

From the repository root, with the pinned archives in `ARCHIVE_DIR`:

```sh
bash tools/sqlite-wasm/check-get-varint-three-byte.sh ARCHIVE_DIR WORK_DIR
```

The script rebuilds the pinned reactor and quotation, checks the original
function record, and compiles both the one- and three-byte reader proofs.
The ordinary downstream import checks overlong zero and the three-byte
canonical endpoints 16384 and 2097151. The fixtures overlap all three
input bytes with the eight-byte output, use distinct caller and callee
memory bindings, and check sentinels on both sides of the destination.
