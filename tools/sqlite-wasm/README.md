# SQLite 3.54.1 WASI reactor in Lean

This fixture builds the upstream SQLite 3.54.1 amalgamation as a stripped,
single-threaded `wasm32-wasi` Preview 1 reactor with in-memory temporary
storage, WAL omitted, and loadable extensions omitted. It exports a small C
API surface for in-memory SQL plus `sqlite3_libversion_number`. The exact flags and compiler, linker,
archive and source SHA-256 pins are in [build.sh](build.sh). The output pin is
in [artifact.sha256](artifact.sha256). The toolchain is WASI SDK 30.0 for
x86-64 Linux, with Clang 21.1.4 at LLVM revision
`222fc11f2b8f25f6a0f4976272ef1bb7bf49521d` and wasi-libc at
`ec0effd769df5f05b647216578bcf5d3b5449725`.
[SQLite releases](https://www.sqlite.org/chronology.html) ·
[WASI SDK release](https://github.com/WebAssembly/wasi-sdk/releases/tag/wasi-sdk-30)

## Reproduce

On x86-64 Linux, from the repository root, with the repository's pinned
Lean/Lake and dependencies, Python 3, GNU time, unzip, tar and Node with
`node:wasi`:

```sh
inputs=$(mktemp -d)
curl -fL https://www.sqlite.org/2026/sqlite-amalgamation-3540100.zip \
  -o "$inputs/sqlite-amalgamation-3540100.zip"
curl -fL https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-30/wasi-sdk-30.0-x86_64-linux.tar.gz \
  -o "$inputs/wasi-sdk-30.0-x86_64-linux.tar.gz"
bash tools/sqlite-wasm/check.sh "$inputs" .lake/sqlite-wasm
```

With the Lake dependencies and the two archives available locally, the build,
generation and replay run offline. [build.sh](build.sh) can build just the Wasm
artifact. [generate.py](generate.py) can generate the Lean sources and quotation
inputs from a cached artifact with the pinned digest. All generated files stay
in the chosen work directory.

## Representation

`SqliteWasm.Object` exposes `SqliteWasm.sqlite : Silmaril.Wasm.Module`.
The generator frames the exact function-type entries and code bodies in
source order, using a 24 KiB code-group budget with a singleton for an
oversize body. It also isolates the version getter and keeps the other
sections together. The individual quotation inputs are fragments for the
syntactic decoder. Only the assembled object has the complete index spaces.

[Quote.lean](Quote.lean) uses the existing
[Core decoder](../../Silmaril/Wasm/Binary/Core/Decode.lean) and
[constructor quotation](../../Silmaril/Wasm/Binary/Quote/Defs.lean), including
packed data bytes. Each group gets an executable Lean declaration. Imports
of the compiled object load those declarations directly. The object can be
used with the existing [Binaryen byte encoder](../../Silmaril/Wasm/Binaryen/Exe/Encode.lean)
and the [module queries](../../Silmaril/Wasm/ModuleParts/Defs.lean). The
generation step needs no WAT or prettyprinted instruction strings. The corpus
build-query inputs cover the same SQLite version getter and provide a public
source seam for the native variants.
[Silmaril quotation](../../docs/projects/wasm-quotation.md) ·
[Native build-query input](../../corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/build-queries/context.c)

## Replay and leaf proof

[Replay.lean](Replay.lean) compares the canonical bytes from the assembled
object, a fresh decode of the original file, and a fresh decode of the
canonical file. All three yield the same 693,311 bytes, pinned in
[canonical.sha256](canonical.sha256). The original has 741,717 bytes and first
differs from this encoding at byte 3,881, counting from zero. The code
section payload shrinks from 679,518 to 631,112 bytes. Every other section's
framed bytes match. The hint-guided padded encoder also yields 741,717 bytes
and differs from the original at byte 3,949. These are executed comparisons.

The object has 1,533 definitions and 23 imported functions. The export
`sqlite3_libversion_number` is function index 289, definition ordinal 266,
with signature `() → i32`. [VersionCheck.lean](VersionCheck.lean) proves by
reduction that the body selected by this export is a single `i32.const` and
that the Binaryen fuel interpreter returns the modeled SQLite version number
from an empty operand stack at fuel 2 for every store and frame. The axiom
audits report `propext`, `Classical.choice` and `Quot.sound`. The proof scope is
the selected Wasm body. [runtime.mjs](runtime.mjs) separately executes the
original and canonical files under Node WASI. Both return 3054001 for the
getter, in agreement with the Lean interpreter, and 42 from a SQL query.

## Quotation cost

Quoting the whole artifact into a single declaration with the pinned Lean
nightly exceeded the declaration recursion limit. On a measured trial,
reading and decoding took 1.7 s and building the constructor term took 0.38 s
before declaration checking failed. A trial with recursion depth 65,536 also
failed. The factored build quotes 33 fragments including metadata, with code
groups batched into four source modules. In a representative run, read and
decode took 1.6 s total, quotation took 0.81 s, and kernel checking plus
Lean compilation took 52 s across the fragments. The largest function body
was 38,390 bytes and needed the raised recursion limit even as a singleton.
The grouped compilation steps peaked near 2.9 GiB RSS per Lean process.
The check script prints per-fragment timings and wall time and RSS by source
module. Timings vary with load and exclude building Lean dependencies.

## Notices

The SQLite amalgamation retains its public-domain dedication. The SDK's
reactor startup and libc come from wasi-libc, and the link includes LLVM
compiler-rt builtins. Keep the upstream notices with redistributed builds.
[SQLite dedication](../../corpus/sqlite/local/COPYRIGHT-sqlite.txt) ·
[wasi-libc notices](https://github.com/WebAssembly/wasi-libc/tree/ec0effd769df5f05b647216578bcf5d3b5449725) ·
[compiler-rt license](https://github.com/llvm/llvm-project/blob/222fc11f2b8f25f6a0f4976272ef1bb7bf49521d/compiler-rt/LICENSE.TXT)
