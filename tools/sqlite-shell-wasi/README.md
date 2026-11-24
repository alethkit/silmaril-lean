# Upstream SQLite shell on WASI Preview 1

This builds SQLite 3.54.1's `shell.c` and `sqlite3.c` into the `sqlite3.wasm`
command. The entry point is `_start`, with SQLite's own CLI argument parsing,
SQL execution and dot commands. It is a separate build from SQLite's standard
browser/library Wasm distribution.

## Build and run

From the repository root on x86-64 Linux, with Bash, GNU coreutils, tar, curl
and the repository's pinned Lean toolchain:

```sh
work=/tmp/sqlite-shell-wasi
tools/sqlite-shell-wasi/build.sh "$work"
tools/sqlite-shell-wasi/check.sh "$work"
```

The build writes `$work/sqlite3.wasm` and verifies its SHA-256. Downloaded
release archives are cached in `$work/downloads`. The default check validates
the core module and its typed imports and exports, compiles the Lean CLI
harness, and runs Wasmtime against the pinned native C corpus shell and
library. These commands need only the files and dependencies on this branch.
[Typed import and export inventory](interface.txt) ·
[Native C corpus provenance](../../corpus/elf/sqlite/x86_64/receipt.json)

The guest itself needs only a WASI Preview 1 command runtime. With the pinned
Wasmtime CLI, the two input modes can be run as follows:

```sh
wasmtime run --argv0 sqlite3 --env HOME=. "$work/sqlite3.wasm" -batch :memory: 'SELECT 6*7;'
printf '.mode list\nSELECT 42;\n' |
  wasmtime run --argv0 sqlite3 --env HOME=. "$work/sqlite3.wasm" -batch :memory:
```

Set `HOME=.` inside a fresh directory to avoid a home-directory warning and
user startup configuration. File-backed commands require an explicit directory
grant such as `--dir=.` before the Wasm path. Use a dedicated directory for
that grant. The check creates its own temporary directories and supplies the
guest only the environment and preopen shown in the runner.

## Source and build profile

- Both C translation units and the header are already in the public corpus.
  `build.sh` verifies their existing hashes. SQLite's released sources are
  in the public domain under the upstream blessing.
  [Source archive and corpus provenance](../../corpus/sqlite/package.toml) ·
  [Source file hashes](../../corpus/sqlite/upstream.sha256) ·
  [SQLite copyright](https://sqlite.org/copyright.html)
- WASI SDK 34.0 uses clang 23.1.0-wasi-sdk and the SDK sysroot. The build
  targets `wasm32-wasip1` at `-O2` with a 1 MiB stack and stripped output.
  Wasmtime 50.0.0 is the execution reference and wasm-tools 1.262.0 validates
  and prints the interface. The release archive SHA-256 values and the built
  module SHA-256 are enforced by the scripts. The Wasmtime and wasm-tools
  releases match the existing Wasm JCO test pins.
  [Build flags](build.sh) · [Release and output pins](pins.sh) ·
  [WASI SDK license](https://github.com/WebAssembly/wasi-sdk/blob/wasi-sdk-34/LICENSE) ·
  [Linked wasi-libc licenses](https://github.com/WebAssembly/wasi-libc/blob/2e6fb9d8ee0cdf9e431fbcabe8af3115de000a13/LICENSE) ·
  [Linked compiler-rt license](https://github.com/llvm/llvm-project/blob/895aa2c896ada719451be2e3673c83da8ddf1141/compiler-rt/LICENSE.TXT) ·
  [Wasmtime license](https://github.com/bytecodealliance/wasmtime/blob/v50.0.0/LICENSE)
- `SQLITE_WASI` selects SQLite's WASI-aware Unix VFS, which defaults to
  `unix-dotfile` locking. The build is single-threaded and omits WAL, dynamic
  extension loading, subprocess pipes, `.shell`/`.system` and external line
  editors. WASI libc emulates signals, process clocks and PID support for
  build compatibility. The checks cover batch streams and a single process
  using the database on a preopened directory. Multi-process locking, crash
  recovery, interactive terminal behavior and profiling are outside the
  checked profile.

## Observations

The [runner](Check.lean) uses the repository's [CLI behavior harness](../../Silmaril/Cli/Io/Run/Defs.lean).
It checks stdout, stderr and exit status byte for byte for SQL in argv and
stdin, early exit via `.exit 7`, shell rejection of invalid SQL and options,
and a write rejected by `-readonly`. Version output identifies the same
SQLite source with a 32-bit width on WASI and 64-bit width on native. The
unknown-option diagnostic includes the respective `argv[0]`. The native
shell returns usage diagnostics for bare `.shell` and `.load`. WASI reports
those commands as unknown.

The guest creates a clean two-page `sample.sqlite` in a preopened directory.
The runner uses those bytes to check four SELECTs against both upstream
shells, verifies that opening the same fixture without a preopen fails, and
checks for new or modified regular files after the read-only cases.

The [Lean adapter](../../Silmaril/Cli/Spec/SqliteShell/Defs.lean) builds argv
for either implementation and reads the CLI harness's `Snap`. Its common view
is ordered column names and integer rows, including signed 64-bit endpoints.
The upstream `-json` mode emits an array of row objects, or zero bytes for an
empty result. The portable Lean shell emits an object with explicit columns
and positional rows. The test supplies ordered, distinct column names for
each fixture. For empty upstream results, the column names come from that
expectation. The harness observes final stdout/stderr, exit status and new
or changed file contents. It has no read trace, deletion trace, or count of
stdin bytes consumed.

### Optional comparison with the native Lean shell

Only the checks enabled by the second argument use the portable shell from
PR #2077. They check four typed SELECT results and its rejection of the
aggregate and DELETE statements. Build `sqlite_lean` at the tested revision
with `lake build --wfail sqlite_lean` and pass its executable to the runner.
[Tested revision](https://github.com/hiloopai/silmaril-lean/tree/2c8a4b344e8751ffe5e2320b55a0aa7d7108dd2f) ·
[Portable-shell PR](https://github.com/hiloopai/silmaril-lean/pull/2077)

```sh
tools/sqlite-shell-wasi/check.sh "$work" /path/to/.lake/build/bin/sqlite_lean
```

The Lean shell requires `--immutable` and a clean, stable 1024-byte snapshot
with the supported schema. The checked overlap consists of an ordered scan,
a projection with limit and offset, a point lookup, and an empty lookup. Both
upstream shells accept the aggregate query that Lean rejects. A write
attempt fails in the upstream shells at SQLite's read-only engine boundary
and in Lean at the SELECT parser. The observations apply to these inputs
and this fixture.
