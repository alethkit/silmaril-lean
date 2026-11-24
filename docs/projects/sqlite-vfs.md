# Abstract SQLite VFS byte I/O

This Lean model covers serial calls on one configured, existing file. The modeled calls
are open, close, read, file size, write, and truncate. Bytes, the current open mode, and a
handle generation form the file view. A handler can have private state and provide a
projection to that view. Each completed exchange exposes a request and its typed reply.
The backing state itself is outside the event stream.

## Contract and source pin

The source is the SQLite Project's **SQLite 3.54.1** amalgamation with source ID
`555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`. The
archive SHA-256 is `0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9`.
The extracted `sqlite3.h` SHA-256 is
`d6c84557261893439b341d2e6c35187ae3ea24fbfd843ad94616f72d89242b8c`.
[Release archive](https://sqlite.org/2026/sqlite-amalgamation-3540100.zip) ·
[Corpus pin](../../corpus/sqlite/package.toml) ·
[Pinned header](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.h)

- The pinned header documents `sqlite3_vfs.xOpen` at lines 1380–1460 and
  `sqlite3_file` and `sqlite3_io_methods` at lines 736–877. SQLite supplies
  storage for the file object. If a failed open leaves `pMethods` non-null,
  SQLite may call `xClose`. This profile chooses failed opens that install no
  handle, requires the requested mode on success, and admits one live token per
  backing. Close retires the generation, so a stale token remains invalid after
  a reopen. Tokens are scoped to their backing. Path resolution, creation,
  temporary files, deletion, and aliases are outside the profile.
  [VFS](https://sqlite.org/c3ref/vfs.html) · [File handle](https://sqlite.org/c3ref/file.html)
- The file methods take signed `sqlite3_int64` offsets and sizes and an `int`
  transfer count. This profile represents raw lengths and offsets in mathematical
  integers and admits positive signed-32-bit counts, nonnegative offsets, and
  exclusive endpoints at most `2^63 - 1`. Write count is the input byte-list
  length. Truncation size must lie in `[0, 2^63 - 1]`. Handle and permission
  checks precede range checks, which precede capacity checks. These are profile
  rules. C buffer allocation, lifetime and ownership belong to a C adapter.
  [I/O methods](https://sqlite.org/c3ref/io_methods.html) ·
  [64-bit integers](https://sqlite.org/c3ref/int64.html)
- The pinned header requires zero-fill of unread bytes on
  `SQLITE_IOERR_SHORT_READ` at lines 847–852. Under a stable snapshot this model
  returns `.ok` with all requested bytes if they fit, or `.shortRead` with the
  available prefix and a zero-filled suffix at EOF. A read beginning past EOF
  has an all-zero short-read buffer. Other errors expose a reason and have no
  buffer observation. The typed outcomes distinguish the selected success,
  short-read, access, capacity and fault cases. SQLite integer return codes and
  caller-owned output memory are outside the model.
  [I/O methods](https://sqlite.org/c3ref/io_methods.html) ·
  [Result codes](https://sqlite.org/rescode.html)
- In the read-write profile, a successful write replaces the specified interval,
  preserves unmodified bytes, and zero-fills any gap before the write. Truncate
  preserves the retained prefix and zero-fills extension to exactly the requested
  size. Each rejected mutation preserves the view. These are in-memory
  semantics. SQLite's pinned Unix `unixTruncate` can round to a configured
  chunk size, and `unixWrite` can perform multiple writes before failing.
  [Pinned Unix methods](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L44297)

## Laws and traces

`Machine.SqliteVfs.Defs` defines the dependent `Response request` family, total `Handler` interface, and
`Trace.Valid` relation. A trace is valid relative to a handler when every reply
and intermediate state agrees with one application of the handler. The sets
`ReadOnlyProfile` and `ReadWriteProfile` impose separate handle, snapshot-read,
and mutation laws on that interface. `ShortReadZeroFill` isolates the EOF
suffix property. Typed routing and trace validity alone allow implementations
that violate it. [Definitions](../../Silmaril/Machine/SqliteVfs/Defs.lean)

`Machine.SqliteVfs.Thms` proves that the two concrete backings satisfy their respective profiles.
`backing_trace_bounds` preserves the minimum of capacity and the maximum
signed file size from an initially bounded state. `readOnly_trace_bytes`
proves that every valid trace of any handler satisfying the read-only profile
preserves the observed bytes. `zeroFill_of_readLaw` derives the EOF
suffix law from the read law. `badShortRead` keeps read-only mutation rejection
and routes the same operations, but fills the unread suffix with 255, which
`bad_violates_zeroFill` and `bad_not_readOnlyProfile` rule out.
[Theorems](../../Silmaril/Machine/SqliteVfs/Thms.lean)

`Containers.SqliteVfs.Thms` uses the landed `Containers.Mach.MachineSem` and `Runtime.ofMachine` directly.
`encode` emits a receive followed by a send per exchange. In `exec_iff`, a
finite machine execution from idle is exactly a list of valid completed
exchanges, optionally followed by one unmatched receive, with the matching
idle or pending state. In `blocked_iff`, the abstract runtime is blocked
waiting for input exactly after the encoded events of a valid completed trace.
The loader supplies the initial state and the transport is a logical event
interface. Connecting an actual server would require framing and decoding its
observations and proving that its finite runs correspond to these events and
handler transitions. Socket and wire codecs, OCI deployment, native VFS
registration, and ELF refinement are outside this correspondence.
[Container trace theorems](../../Silmaril/Containers/SqliteVfs/Thms.lean)

Control-flow evidence for one pinned x86-64 dispatch and the SC mutex/callback
trace address different boundaries. They supply context for the model.
[Dispatch evidence #1128](https://github.com/hiloopai/silmaril-lean/pull/1128) ·
[File-control trace #2070](https://github.com/hiloopai/silmaril-lean/pull/2070)

## Scope and checks

- **File locking and concurrency.** The adapter serializes calls with one
  pending request. SQLite file-lock transitions, shared-memory locks, racing
  clients, and scheduler correctness are outside the model.
- **Failures.** The backing produces deterministic validation, permission,
  and capacity errors. Host faults, partial writes on failure, memory faults,
  and crash behavior are outside the proved profiles.
- **SQLite transactions.** The model sees bytes and handles. Pager, journal,
  and WAL invariants, rollback, and SQL transaction guarantees require
  separate specifications.
- **Sync and durability.** There is no `xSync` operation. The normal, full,
  and data-only sync semantics and persistence across a crash are outside
  the model. [I/O methods](https://sqlite.org/c3ref/io_methods.html)

Run these checks from the repository root with the pinned Lean toolchain.

```sh
lake build --wfail +Silmaril.Containers.SqliteVfs.Checks
make check CHECK_TARGETS=+Silmaril.Containers.SqliteVfs.Checks
```

The check module builds read-only and read-write fixtures through the abstract
runtime, a finite trace ending in a pending call, and the deliberate bad
short-read trace. It prints the transitive axioms of the public theorems.
