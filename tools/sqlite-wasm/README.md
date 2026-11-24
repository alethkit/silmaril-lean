# Custom SQLite 3.54.1 WASI library reactor in Lean

This fixture custom-configures the upstream SQLite 3.54.1 amalgamation as a
stripped, single-threaded `wasm32-wasi` Preview 1 library reactor with
in-memory temporary storage and SQLite's WAL and loadable extension features
disabled. It exports `_initialize`, a small C API for in-memory SQL and
`sqlite3_libversion_number`. SQLite publishes its official WebAssembly and
JavaScript distribution separately. The repository's SQLite shell build
compiles `shell.c` and exposes a WASI command at `_start`.
[Official SQLite web distribution](https://www.sqlite.org/2026/sqlite-wasm-3540100.zip) ·
[WASI shell build](https://github.com/hiloopai/silmaril-lean/pull/2081)

The exact flags and the compiler, linker, archive and source SHA-256 pins
are in [build.sh](build.sh). The output pin is in [artifact.sha256](artifact.sha256).
The toolchain is WASI SDK 30.0 for
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
artifact. [quote.sh](quote.sh) generates and compiles the Lean object from
a cached artifact with the pinned digest. [generate.py](generate.py) runs
just source generation. All generated files stay in the chosen Lean root.

## Artifact profiles

The version 1 JSON manifest has five fields. `schema_version` is the integer
1, `sqlite_version` is the upstream release, both SHA-256 fields are lowercase
hex, and `profile` selects the expected function export and Lean namespace.
The generator checks the Wasm digest and export. The producing build scripts
establish provenance by checking the source and toolchain pins.
[Reactor manifest](reactor.json) · [Shell build and runtime tests](https://github.com/hiloopai/silmaril-lean/pull/2081)

| Profile | Entry point in the pinned artifact | Generated module | Defined / imported functions |
| --- | --- | --- | --- |
| `wasi-preview1-reactor` | `_initialize` at 25 | `SqliteWasm.Object` | 1,533 / 23 |
| `wasi-preview1-command` | `_start` at 28 | `SqliteShellWasi.Object` | 2,010 / 27 |
| `sqlite-web` | Start section at 36 | `SqliteWebWasm.Object` | 2,706 / 35 |

For a cached reactor, run the shared entry point from the repository root.

```sh
tools/sqlite-wasm/quote.sh tools/sqlite-wasm/reactor.json \
  .lake/sqlite-wasm/sqlite3.wasm .lake/sqlite-wasm/lean/SqliteWasm
```

For the command produced by the shell task, supply its own manifest with
`profile` set to `wasi-preview1-command`.

```json
{
  "schema_version": 1,
  "sqlite_version": "3.54.1",
  "source_archive_sha256": "0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9",
  "artifact_sha256": "b71ec78557631b7a31d27ede9336aa22af9fce926712d2416d9872f18198d2a3",
  "profile": "wasi-preview1-command"
}
```

```sh
tools/sqlite-wasm/quote.sh "$work/command.json" "$work/sqlite3.wasm" \
  "$work/lean/SqliteShellWasi"
```

Both profiles use the SQLite 3.54.1 amalgamation. The command's build uses
WASI SDK 34.0, while the reactor uses 30.0. The command's argument, stream,
exit status and file behavior are checked by the shell tool. The reactor's
test invokes its exported C API. Both use the same stripped Core section IDs
in order, `1, 2, 3, 4, 5, 6, 7, 9, 10, 11`. Version 1 expects this section
layout. Each generated `Object` exposes ordinary Lean definitions `sqlite` and
`entrypointIndex` under the profile's namespace. The [official web profile](../sqlite-web-wasm/README.md)
uses `SqliteWebWasm.Object` and takes its entry point from the Start section.
An ordinary `import` makes the quoted definitions available to theorem files.

The generated objects can be imported together using one Lean search path.
The web profile also imports `env.memory`. For the shell, encoding the
assembled object and encoding a fresh decode of the original produce the
same 1,383,762 canonical bytes. The 1,473,955-byte linker output first
differs at byte 4,849, counting from zero. Wasmtime 50.0.0 reports SQLite
3.54.1 and returns `42` from `SELECT 6*7;` on both shell files.

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
and differs from the original at byte 3,949. The canonical agreement is
evidence from executing the decoder and encoder. The two offsets record
where the respective byte sequences first depart from the linker output.

The object has 1,533 definitions and 23 imported functions. The export
`sqlite3_libversion_number` is function index 289, definition ordinal 266,
with signature `() → i32`. [VersionCheck.lean](VersionCheck.lean) proves by
reduction that the body selected by this export is a single `i32.const` and
that the Binaryen fuel interpreter returns the modeled SQLite version number
from an empty operand stack at fuel 2 for every store and frame. The axiom
audits report `propext`, `Classical.choice` and `Quot.sound`. Kernel-checked
claims cover the selected body and its fuel-interpreter result.
[runtime.mjs](runtime.mjs) separately executes the
original and canonical files under Node WASI. Both return 3054001 for the
getter, in agreement with the Lean interpreter, and 42 from a SQL query.

## Kernel checks against the original bytes

[ArtifactCheck.lean](ArtifactCheck.lean) checks the version export and
matches complete defined functions at indices 289, 434, 530 and 547 against
the original linker output. Presence and equality give the same type index,
locals and instruction tree on both sides.

[ArtifactEntries.lean](ArtifactEntries.lean) reads the unmodified artifact
from packed byte literals. It checks the header and section framing, decodes
the import section to count function imports, and locates each definition
by walking the Function and Code vectors. It uses the Core decoder to
parse the selected code entry. Other code bodies are skipped by size.
The stripped artifact has no symbol names for the internal helpers. The
source-level names come from the linked-build evidence in
[#2093](https://github.com/hiloopai/silmaril-lean/pull/2093).

The SHA-256 check and file ingestion run outside the kernel. Lean checks the
equations over the resulting byte literals and quoted AST. The theorem scope
ends at the selected records. Complete decode and original-to-canonical replay
remain separate executable checks.
[Recheck a quoted artifact](check-artifact.sh)

## One-byte varint behavior

[PutVarintCheck.lean](PutVarintCheck.lean) checks the signature and first
block of the quoted function 530. `putVarint_oneByte` proves a Core
small-step execution of `call 530` for every unsigned value from 0 through
127. The premises bind the caller's function slot to the quoted code and
its runtime signature, and map the callee's memory 0 to a memory instance
with one writable byte at the supplied i32 address.

The execution returns the length of `Silmaril.Formats.Sqlite.Varint.encode`,
splices its single byte into that memory and restores the caller frame.
The proof follows the first block through the packed store and early
return. The original-artifact link is `originalPutVarintFunction` in
[ArtifactCheck.lean](ArtifactCheck.lean). The [differential fixture](../sqlite-wasm-varint/README.md)
exercises encoding and decoding across widths 1 through 9.

## Executions through the long varint helper

[VarintWitness.lean](VarintWitness.lean) checks two concrete encodes starting
in function 530 and calling the quoted helper at index 547. A typed Core
fixture binds the two original function records to store addresses 0 and 1,
maps call slot 547 to address 1, and supplies memory 0 with one page and a
stack pointer of 128. The output address is 16. The fixture preserves the
quoted instructions and uses its own runtime bindings.

The kernel evaluates `runInvokeK` at `16384` and `0x01000000000000ad`.
The final stores match the corresponding `Varint.encode` output splices,
and the calls return 3 and 9, respectively. The three-byte case also writes
`00 80 81` to scratch offsets 118 through 120. The nine-byte case preserves
the rest of memory. `runInvokeK_eq` and `runInvoke?_steps_noHost` transfer both
checked runs to Core small-step reachability. These witnesses cover the
two values and the fixture's typed store.

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
