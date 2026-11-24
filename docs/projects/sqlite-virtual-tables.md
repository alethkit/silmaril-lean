# SQLite read-only virtual tables

Import `Silmaril.Formats.Sqlite.VirtualTable.Thms` for the contract or
`Silmaril.Formats.Sqlite.VirtualTable.Backed.Thms` for the one-column client.
Both use Lean's signed `Int64` at the value and rowid boundaries. They build
with the repository's pinned Lean toolchain and have no dependencies on the
SQLite file reader, VFS, or shell. A future VDBE adapter can embed the column
results in its integer storage class and supply evaluated registers as
`xFilter` arguments.

The contract follows the [SQLite virtual-table guide](https://sqlite.org/vtab.html),
the [module callback table](https://sqlite.org/c3ref/module.html), and
[planner inputs and outputs](https://sqlite.org/c3ref/index_info.html).
The source baseline is [SQLite 3.54.1](../../corpus/sqlite/package.toml), source ID
`2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`.
The repository pins [the amalgamation input hashes](../../corpus/sqlite/upstream.sha256).
See the [pinned header](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.h#L7739),
[planner validation](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L174140),
and [VDBE cursor dispatch](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L104947).

## Contract

- `Relation` is the list of typed rows. `Snapshot` fixes the backing rows and
  requires distinct rowids. An `Index` is an executable scan strategy
  named by `idxNum` and optional `idxStr`. Its candidate stream can be
  in a different order and may include rows failing residual predicates.
- The lifecycle admits one eponymous-only module and one connected table
  instance per model connection. Registration, `xConnect` and `xDisconnect`
  surround any number of open cursor handles. `xOpen` yields an unfiltered
  cursor. `xClose` retires it, and a disconnect or connection close requires
  all handles to have been retired. There is no `xCreate` or `xDestroy` in
  this eponymous-only profile.
- `xBestIndex` sees normalized integer comparisons `=`, `<`, `<=`,
  `>`, `>=` against rowid or declared columns, the usability of each
  right-hand side, and an optional single rowid sort direction. It can
  decline a candidate with `noPlan` (the planning use of
  `SQLITE_CONSTRAINT`). In a plan, slots are contiguous and one-based, with
  slot `k+1` selecting `argv[k]` at `xFilter`. Each selected constraint
  must be in bounds, usable, and selected once. Absent terms get
  `argvIndex=0` and no omit hint. The profile admits omit hints only
  in the first 16 argument slots and for the first 16 constraint entries.
  The guide documents the slot limit. The pinned planner also gates the
  ordinary omit mask by constraint position. A hint grants permission
  to skip a recheck, and SQLite may still recheck it.
- `xFilter` positions at the first candidate or EOF, replaces a previous
  scan, and invalidates the position on failure. `xNext` advances one row,
  including the transition from the final candidate to EOF. `xEof` is a
  Boolean position check used after successful positioning. `xColumn`
  reads a zero-based declared column and `xRowid` reads the separate
  signed rowid. Calls past EOF, before positioning, after close, or with
  invalid column/handle numbers have distinct model errors. The pure
  position check returns true when there is no current row. The pinned
  VDBE calls `xEof` after successful `xFilter` or `xNext`.
  `ScanTrace` accounts for each row and the terminating EOF.
- The error model propagates a scan-provided status and distinguishes it
  from invalid plans and lifecycle/position diagnostics. The pure
  in-memory `xNext` and read operations have no implementation I/O
  failure. The diagnostics describe calls in Lean and have no assigned
  SQLite numeric codes.

## Guarantees

`checkHonesty_iff` connects the finite check to `Honest`. It checks layout, row
provenance and uniqueness, and preservation of all matching rows with their
multiplicity. Every emitted candidate must pass each omitted term, even a
candidate later discarded by residual predicates. A consumed rowid order
must hold on the whole stream. `finish_perm` proves preservation of the
matching rows. With a requested order, `finish_eq_reference` proves equality
with reference filter-then-sort, whether the plan consumes the order or the
caller sorts. These are obligations per snapshot and evaluated invocation.
`Table.runChecked` is a finite audit runner, and `Table.run` is the execution
path that trusts the planner claims.

`Backed.query_correct` proves successful execution without the audit for
every one-column snapshot with unique rowids, both sort directions, and all
signed-64-bit bounds for the following query.

```sql
SELECT rowid, value FROM backed
WHERE rowid >= ?1 AND value < ?2
ORDER BY rowid ASC
```

The module requests the ceiling in slot 1 and the lower bound in slot 2.
It enforces the lower bound, leaves the ceiling for residual checking, and
consumes the requested order. Regressions reject a false omit claim for
the ceiling, a reversed scan claiming to consume the order, and a scan
missing a matching row. They also exercise argument layout and cursor failure,
refiltering, EOF, and handle retirement.

## Reproduce the checks

```sh
lake build --wfail +Silmaril.Formats.Sqlite.VirtualTable.Backed.Thms
tests/formats/sqlite-virtual-table/run.sh
```

The regression script audits transitive axioms against `policy.toml` and
builds a native C fixture against the hash-checked SQLite amalgamation.
SQLite calls the fixture through a real read-only `sqlite3_module`. For
72 bound/direction combinations on a six-row fixture, the script compares
the positioned row stream and final SQL results with Lean. The C probe
also compares final rows with an ordinary SQLite table, checks that SQLite
uses no sorter for the virtual scan, checks lifecycle counts and EOF, and
exercises an `xFilter` type error. The fixture includes signed-64-bit extremes,
empty results and duplicate column values. The evidence for native execution is limited to these differential tests.

The Lean profile covers one immutable scan at a time in a query. SQL parsing, affinity, coercion, NULL semantics, expressions, joins,
multiple sort keys, collations, IN/LIMIT/OFFSET, DISTINCT or aggregate
planning, cost-based plan selection, C allocation and ABI behavior, writable
callbacks, transactions, and concurrency are outside the profile. The native fixture
accepts only the demonstrated comparison, order and integer argument
profile. The Lean regressions exercise cursor interleaving.
