# Read-only SQLite shell in Lean

```sh
lake build --wfail sqlite_lean
.lake/build/bin/sqlite_lean --immutable sample.sqlite \
  'SELECT id, amount FROM sample ORDER BY id LIMIT 3;'
```

The binary reads a regular, fixed SQLite snapshot and writes a JSON object
with ordered `columns` and integer `rows`. Its table profile is exactly one
table declared as follows.

```sql
CREATE TABLE sample(id INTEGER PRIMARY KEY, amount INTEGER NOT NULL) STRICT
```

The file must have two 512-byte pages, UTF-8, no reserved space or freelist,
and packed table leaves. The catalogue must contain the exact CREATE text.
The row decoder checks the serialized NULL placeholder for the rowid alias
and requires an INTEGER amount. The CLI requires `--immutable` and refuses
journal, WAL and shared-memory sidecars at the supplied and canonical paths.
The caller supplies a stable snapshot. There is no live snapshot acquisition,
locking, or recovery.

There is one SELECT statement. It accepts `*`, either column, or both
columns in either order, optional `WHERE id = <signed 64-bit integer>`,
optional `ORDER BY id [ASC|DESC]`, and optional `LIMIT n [OFFSET n]` with decimal
natural numbers. Keywords and these unquoted identifiers are case
insensitive. A final semicolon is optional. The default scan order is ascending rowid. Descending order reverses
the bounded scan before LIMIT and OFFSET. Writes, other SQL and malformed images produce a nonzero status
and no JSON result.

The VM executes a table scan or rowid seek. Projection and slicing are
applied to its result. Its value and table-read interfaces depend only on
Lean and the existing public bytes API. Lean checks correspondence of
instruction execution with its step relation and existence of finite
traces for fuel-bounded runs. The VM and proofs are by Jad-Elkhaleq
Ghalayini, distributed under this repository's MIT license. The native
differential checks do not establish equivalence of the entire SQL parser,
the C VDBE, or SQLite's storage implementation.

```sh
make check CHECK_TARGETS=sqlite_lean
```

The regression generates a fresh database with pinned SQLite 3.54.1 and
compares the actual Lean shell's exit status, columns and typed rows to
native results. It also checks rejection and file preservation.
[SQLite source and artifact provenance](../../corpus/sqlite/package.toml)

The opcode descriptions were cross-checked against public SQLite
`src/vdbe.c` at `1e4e45df2465b56feeccc75f413be502768f95a9`,
SHA-256 `76c12ba1355923bab5a54244e2bad2ab4643f2d319df627d5266c0a8f0661658`.
[Pinned VDBE reference](https://github.com/sqlite/sqlite/blob/1e4e45df2465b56feeccc75f413be502768f95a9/src/vdbe.c)
