# zlib 1.3.1 Adler-32 Core Wasm fixture

This fixture compiles upstream `adler32.c` with WASI SDK 34.0
(clang 23.1.0-wasi-sdk) on x86-64 Linux. The stripped output is a 1,137-byte
WebAssembly Core module with no imports or start function. It exports one
32-bit linear memory and the C functions `adler32_z` (index 0) and
`adler32` (index 1), each with type `(i32, i32, i32) → i32`. LLVM's
linker retains only these two function bodies. The command uses the WASI
SDK sysroot for headers and links with `-nostdlib`.
[Build and source pins](build.sh) · [Wasm SHA-256](artifact.sha256)

## Reproduce

From the repository root, download the two release archives. The build
runs offline with these files and verifies the archive, source files and
output by SHA-256.

```sh
work=$(mktemp -d)
curl -fL https://zlib.net/fossils/zlib-1.3.1.tar.gz -o "$work/zlib-1.3.1.tar.gz"
curl -fL https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-34/wasi-sdk-34.0-x86_64-linux.tar.gz \
  -o "$work/wasi-sdk-34.0-x86_64-linux.tar.gz"
tools/zlib-wasm/build.sh "$work" "$work/adler32.wasm"
cmp "$work/adler32.wasm" tools/zlib-wasm/adler32.wasm
tools/zlib-wasm/check.sh
```

With the repository's pinned Lean toolchain, Lake dependencies and Node
available, the check hashes the checked-in fixture, parses it with the
ordinary Lean Core decoder, runs the Core validator, and checks the
exported indices and types. A one-byte truncation must be rejected. In a
separate runtime check, Node instantiates the module and checks both
functions on zlib's null-buffer initialization and three byte vectors,
including input beyond the 5,552-byte loop boundary.

The parser and runtime results are executable observations. The comparison
covers those vectors and the linked checksum exports. The general
Adler-32 checksum model lives in `Silmaril.Formats.Compression.Checksum`.
[Adler-32 implementation model](../../Silmaril/Formats/Compression/Checksum/Adler32.lean) ·
[RFC 1950](https://www.rfc-editor.org/rfc/rfc1950#section-2.2)

The fixture uses unmodified zlib 1.3.1 sources and retains the upstream
zlib notice. [zlib license](LICENSE-zlib) ·
[Official release archive](https://zlib.net/fossils/zlib-1.3.1.tar.gz)
