# SQLite page fill over a VFS trace

`Machine.SqliteVfs.PageRead.fill` reads one physical page into a caller-owned
vacant slot. The slot map distinguishes unowned slots, owned vacancies, and
resident pages. The caller supplies a file handle, a one-based page number,
and the physical page size. The admission check uses
`(number - 1) * size` and the VFS's signed transfer bounds. The caller derives
the page size from the file header for a real database.
[Page fill definitions](../../Silmaril/Machine/SqliteVfs/PageRead/Defs.lean) ·
[VFS contract](sqlite-vfs.md)

An unavailable slot or invalid address returns without any VFS exchange.
Otherwise, the outcome retains the single dependent read exchange and the
handler's resulting state. A full response of exactly the requested length
turns the vacancy into a resident page. A short read, wrong length, or VFS
error leaves the cache unchanged. The raw exchange still exposes the short
read's zero-filled bytes when supplied by the backing.

- `fill_trace` proves the outcome's VFS trace is valid from the supplied
  file state to the returned state for every total handler.
- `fill_other` frames any other slot. `fill_rejected` frames the entire
  cache on error. `fill_success` establishes prior ownership, address
  admission, and installation of the returned page in the target slot.
- `readOnly_fill` gives the exact complete-page and short-read outcomes
  for the landed read-only backing. Its premises apply to one operation
  and require a vacant owned slot, an admitted address, and a live handle.
  The requested interval and file length select the branch. Both branches
  preserve the backing state.
  [Public theorems](../../Silmaril/Machine/SqliteVfs/PageRead/Thms.lean)

The pinned SQLite 3.54.1 non-WAL `readDbPage` uses the same offset formula.
It converts `SQLITE_IOERR_SHORT_READ` to `SQLITE_OK`. This strict boundary
serves complete existing pages and rejects a short read before installing
a resident slot. The C routine's lock precondition and page-one
`dbFileVers` update are outside this model, as are WAL frame lookup,
cache eviction, dirty pages, shared slot ownership, and native memory
layout. The source hash is
`0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52`.
[Pinned readDbPage](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L62034) ·
[Dispatch evidence](sqlite-vfs-read.md)

## Attachment points

- A page cache would dispatch a miss through `fill` and expose the resident
  slot to its borrower. Hits, release, and freshness across file mutations
  belong to that cache.
- A B-tree adapter can check the resident bytes against the corresponding
  `File.Image.page?` view, then feed a page decoder. Its row lookup and
  scan results would implement the existing B-tree `ReadModel`.
  [File view](../../Silmaril/Formats/Sqlite/File/Defs.lean) ·
  [B-tree read model](../../Silmaril/Formats/Sqlite/BTree/Query/ReadModel/Defs.lean)
- VDBE cursors consume table reads at the row level. The planner supplies
  a scan or seek program to the VDBE. The shell parses the supported SQL
  into a query and selects that program. These layers need no direct
  access to the slot map.
  [VDBE](../../Silmaril/Formats/Sqlite/Vdbe/Defs.lean) ·
  [SQL front end](../../Silmaril/Formats/Sqlite/Shell/Defs.lean)

## Checks

```sh
lake build --wfail +Silmaril.Containers.SqliteVfs.PageRead.Checks
make check CHECK_TARGETS=+Silmaril.Containers.SqliteVfs.PageRead.Checks
```

The fixtures exercise an exact read followed by an EOF read, local
ownership and address rejection, and rejection of a malformed full
reply whose handler state changed. The two read exchanges also form a
checked input-blocked trace of the landed container runtime.
[Check module](../../Silmaril/Containers/SqliteVfs/PageRead/Checks.lean)
