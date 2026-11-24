# Differential check of the reactor's compiled SQLite varint helpers

This follow-up checks two function bodies from the custom SQLite 3.54.1
WASI library reactor. The pinned build can emit a linker map alongside
the SHA-256-checked Wasm. The map locates the compiled functions, and
[prepare.py](prepare.py) checks their entry sizes and indices against the
original Code section. The map locates the existing version export at
index 289 as a further check of the offset convention.
[Reactor build and pins](../sqlite-wasm/README.md)

| SQLite symbol | Wasm function index | Original file offset | Code entry bytes |
| --- | ---: | ---: | ---: |
| `sqlite3GetVarint` | 434 | `0x2d51d` | 404 |
| `sqlite3PutVarint` | 530 | `0x38174` | 79 |

Offsets and sizes include the body's size prefix. Add the Code section's ID and length framing to the linker map offsets to
obtain the file offsets shown above. The test copy adds two exports
at these indices and checks that every other framed section is
byte-identical to the pinned binary. The test reports a SHA-256 for
each original Code entry.

## Reproduce

Use the two SHA-pinned archives from the reactor recipe, the repository's
pinned Lean and Lake, and Node with `node:wasi`.

```sh
tools/sqlite-wasm-varint/check.sh ARCHIVE_DIR .lake/sqlite-wasm-varint
make check CHECK_TARGETS=sqlite_file_format_compatibility
```

The first check runs offline with the archives and Lake dependencies
available locally. [Vectors.lean](Vectors.lean) evaluates `Varint.encode`
and `Varint.read?` to produce the expected observations. It covers width
transitions, unsigned extremes, overlong encodings and all 256 values
for the ninth octet. The second check exercises the landed
file-format tests with native SQLite fixtures. [Lean varint oracle](../../Silmaril/Formats/Sqlite/Varint/Defs.lean) ·
[Raw file-format compatibility cases](../../tests/formats/sqlite-tranche/Compatibility.lean) ·
[SQLite file format](https://www.sqlite.org/fileformat.html#b_tree_pages)

[runtime.mjs](runtime.mjs) invokes the compiled helpers in an initialized
Node WASI reactor. It compares the encoded byte sequence, decoded
unsigned value, consumed width, and the bytes surrounding each write
in the allocated region. The fixture checks 534 encodes and 797 complete
decodes across widths one through nine. The decoder receives complete inputs and a
disjoint, eight-byte-aligned result slot. The Lean vector generator
checks truncated inputs separately because the C decoder takes a
pointer and assumes a complete varint.

## Correspondence statement

The encoder statement is that a call at index 530 with a `UInt64` input
and a writable nine-byte destination returns the size of `Varint.encode`
and writes those bytes. The decoder statement is that, when
`Varint.read?` succeeds on a readable input span, a call at index 434
returns the consumed width and writes the corresponding value as one
little-endian 64-bit word in its disjoint aligned result slot. Both
statements use an initialized reactor state and valid nonoverlapping
memory for the observations. A proof can follow the compiled bodies
through the Core memory and call semantics, including the encoder's
call to `putVarint64` and the decoder's full-octet final branch. This
slice supplies concrete observations of the Wasm calls.
