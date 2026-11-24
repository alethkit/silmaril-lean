# SQLite file-control validation fragment

The call-level Lean port follows one forwarding branch of `sqlite3_file_control`.
The abstract specification and port each schedule one thread at a time. In both,
a caller acquires the connection mutex, dispatches one VFS operation, restores
the protected busy-handler count, releases the mutex, and returns the callback's
signed 32-bit status. The callback may report an error and change the count.
Other callers can acquire after release, even before the first caller returns.

`runRefines` preserves the entire visible event list and the projected final
configuration for every finite port run. The two private-cache B-tree calls are
silent. An attempted enter while owned has no enabled step, and only the owner
can dispatch, restore, or release. Returning an error uses the same restore and
release steps as returning success. A VFS reply is an input to the model, and
the handler's internal execution is represented by a single dispatch-and-return
step. [Definitions](../../Silmaril/Machine/SqliteControl/Defs.lean) ·
[Theorem](../../Silmaril/Machine/SqliteControl/Thms.lean) ·
[Kernel regressions](../../Silmaril/Machine/SqliteControl/Checks.lean)

## Source and observation boundary

The port admits one live connection with a real mutex, a private-cache, already
opened main database, a live `sqlite3_file` with an installed `xFileControl`
handler, and custom opcode 1001. It takes the default database argument
(`zDbName == NULL`) and an unused argument pointer (`pArg == NULL`). Calls start
outside the mutex. The admitted handler returns normally without re-entering
SQLite through this connection. The model represents one invocation per
participating thread. It omits wrapper precondition failures, other APIs and
branches, recursive locking, fairness, callback internals, pointer lifetime,
and memory effects outside the connection's busy count. The source load of
`nSave` is grouped with dispatch. The restoration of `db->busyHandler.nBusy` is
a separate step. Negative statuses and extended result codes use the same
pass-through rule as other signed statuses.

The source is SQLite 3.54.1, source ID
`2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`.
The official archive SHA-256 is
`0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9`.
The tracked amalgamation matches the archive's `sqlite3.c` byte for byte and has
SHA-256 `0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52`.
The forwarding branch is at line 192575, `sqlite3OsFileControl` at 27794,
and the enter/try/leave wrappers at 30692–30726. The reference build uses
`SQLITE_THREADSAFE=1`. Its x86-64 shared-library SHA-256 is
`fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8`.
[Upstream archive](https://sqlite.org/2026/sqlite-amalgamation-3540100.zip) ·
[Corpus provenance and flags](../../corpus/sqlite/package.toml) ·
[Amalgamation](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L192575) ·
[SQLite file-control API](https://sqlite.org/c3ref/file_control.html)

The scope of the theorem is the hand port. It supplies a reference for a future
source-language simulation with C field, callback-table, initialization, and
lifetime obligations. The C probe exercises the actual pinned source on one
thread with a synthetic VFS method and checks status, callback ownership,
restoration, and release. Its debug build is a separate artifact from the
release ELF.

## Function-by-function follow-up

| Candidate | Next observation to validate |
| --- | --- |
| `sqlite3_mutex_enter`, `sqlite3_mutex_try`, `sqlite3_mutex_leave` | Null and live-handle dispatch, then backend behavior, including a distinguishable busy result for try and the release ownership precondition. Record backend, recursive/fast type, and live-handle relation. |
| `sqlite3_extended_result_codes` | Under acquire/release, write `0xff` or `0xffffffff` to `errMask` and return `SQLITE_OK` on a live handle. Add invalid-handle observation only for a build with API armor. |
| `sqlite3_file_control` forwarding branch | Validate the port's save, call, restore and return against the admitted C branch and compare those observations to an ABI-level cut of the pinned ELF. Extend with missing methods (`SQLITE_NOTFOUND`) and missing schema (`SQLITE_ERROR`) as separate cuts. |
| `sqlite3OsRead`, `sqlite3OsWrite`, `sqlite3OsSync` | Admit a live method table and typed buffers. Check read bytes and short-read zero fill, write status and effects, and the zero-flags sync branch separately. Give each handler its own contract. |

The merged `sqlite3_mutex_leave` and inlined non-WAL `xRead` developments check
fixed x86-64 instruction cuts ending at return or handler entry. Read dispatch
attests the argument registers and pushed continuation. The cuts supply ABI
and footprint evidence. Handler bodies, loader/linking, and C-to-binary
correspondence need separate checks. This model imports neither development.
For the next binary validation, pin source, flags, compiler, linked ELF,
and exact cut bytes. Reconcile calls and returns, heap and callback slots,
observable addresses and error results under explicit admission conditions.
[Mutex boundary #1126](https://github.com/hiloopai/silmaril-lean/pull/1126) ·
[VFS read boundary #1128](https://github.com/hiloopai/silmaril-lean/pull/1128) ·
[SQLite VFS methods](https://sqlite.org/c3ref/io_methods.html)

## Concurrency validation plan

1. **SC model and native dispatch.** Enumerate two callers' per-thread steps,
   including success, `SQLITE_BUSY`, extended I/O errors and attempts to enter
   while owned. Check event order and final count using the model. On a pinned
   `SQLITE_THREADSAFE=1` build with `SQLITE_OPEN_FULLMUTEX` and private cache,
   use a barrier inside a test VFS callback to hold the first caller while a
   second begins. Record the second caller's first callback entry and each
   status. Require at most one callback active and restoration before the next
   dispatch. Use a timeout to diagnose a stuck test. A finite test measures the
   recorded run. Repeat on two connections with separate database files as a
   control. SQLite serializes calls sharing a serialized connection. In
   multi-thread mode (`SQLITE_THREADSAFE=2` by default, or chosen at
   initialization or by connection flags), keep each connection and its
   derived objects confined to one caller at a time. `SQLITE_THREADSAFE=0`
   compiles mutexes out and cannot be switched to serialized mode. A custom
   mutex implementation needs its own contract.
   [SQLite threading modes](https://sqlite.org/threadsafe.html)
2. **Native memory ordering.** Reproduce the assembly store-buffering litmus
   with and without its locked variant using the existing Lean x86-TSO model.
   The unprotected both-zero outcome is admitted by TSO. Add a handoff test in
   which one holder writes a protected payload then releases and the next
   successful acquirer reads it. Check that the next holder observes the
   published payload for the exact compiled pthread implementation. To connect
   that result to these SC steps, supply the primitive implementation,
   call-boundary and ownership certificates for SQLite's chosen mutex kind,
   code and runtime. The public `lll_lock` bridge supplies a method and a
   specific nonrecursive primitive result. SQLite's recursive connection
   mutex and callback re-entry require their own evidence.
   [TSO/SC bridge](../../Silmaril/Process/Mt/Drf/Prim/Thms.lean) ·
   [Public litmus theorems](../../Silmaril/Process/Mt/Drf/Litmus/Thms.lean) ·
   [x86-TSO paper](https://www.cl.cam.ac.uk/~pes20/weakmemory/cacm.pdf)
3. **Wasm builds.** The upstream 3.54.1 browser recipe sets
   `SQLITE_THREADSAFE=0` and omits shared cache. Test one SQLite instance
   confined to its worker and check the selected VFS separately, including any
   host-side worker or OPFS coordination. A custom shared-memory build needs
   its own toolchain, pthread/atomics/wait/notify and embedding contract. First
   inspect the actual Wasm for shared memory and atomics. Then run a two-worker
   payload handoff and check the specific atomics under the Wasm threads memory
   model. The public Lean Core memory profile covers one memory with plain
   i32 loads/stores, and the host-call relation can expose VFS imports and
   outcomes. The WasmFX thread examples model cooperative continuation
   scheduling. These are separate boundaries from shared-memory pthreads.
   [Pinned upstream build](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/ext/wasm/GNUmakefile#L406) ·
   [Core memory profile](../../Silmaril/Wasm/Execution/Core/MemoryProfile/Defs.lean) ·
   [Wasm host calls](../../Silmaril/Wasm/Abstract/HostEval/Defs.lean) ·
   [WasmFX example](../../Silmaril/Wasm/FX/Examples/Threads/Defs.lean) ·
   [Wasm threads proposal](https://github.com/WebAssembly/threads/blob/main/proposals/threads/Overview.md)
4. **File/process locks and crash durability.** Use two independent processes
   opening the same fresh database through the exact VFS. In rollback-journal
   mode, hold a writer transaction with `BEGIN IMMEDIATE`, require a competing
   writer with zero timeout to get `SQLITE_BUSY`, end the first transaction,
   and retry the second. Add WAL schedules for reader snapshots and
   `xShmLock` separately. Interpose VFS write, sync, truncate, and delete,
   inject I/O failures at each boundary, and simulate lost or reordered writes
   according to a stated filesystem and sync contract. Reopen from the
   surviving bytes, check `integrity_check` and the allowed committed state
   for the journal mode and synchronous setting. A native process kill checks
   process restart behavior. A power-loss model also needs stable-storage
   assumptions. Connection mutex events alone specify neither the file
   lock protocol nor the persistence order.
   [Rollback locking](https://sqlite.org/lockingv3.html) ·
   [WAL](https://sqlite.org/wal.html) ·
   [Atomic commit](https://sqlite.org/atomiccommit.html)

A future Lean SQLite release can use the public port as a source-side comparison
point for effectful adapters. Relate immutable file snapshots to admitted VFS
reads and keep pure SQL and VM results in a separate relation. If that
implementation adds effects, relate the actual protected connection fields and
VM operations to explicit state edits, and introduce a persistence relation for
observations after reopen. This module is independent of any SQLite shell,
runtime, or release target.

## Checks

```sh
lake build --wfail +Silmaril.Machine.SqliteControl.Checks
make check CHECK_TARGETS=+Silmaril.Machine.SqliteControl.Checks
(cd corpus/sqlite && sha256sum -c upstream.sha256)

scratch=$(mktemp -d)
cc -O0 -DSQLITE_THREADSAFE=1 -DSQLITE_DEBUG -pthread \
  -I corpus/sqlite/upstream/sqlite-amalgamation-3540100 \
  scripts/sqlite-control/probe.c -ldl -lm -o "$scratch/probe"
"$scratch/probe" "$scratch/probe.sqlite"
rm -r "$scratch"
```

The probe expects statuses `0`, `5`, and `266`, one callback per call, and
a restored count of `7` in every case.
