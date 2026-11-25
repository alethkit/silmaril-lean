# Page-byte agreement after a bounded VFS mutation

The cache-hit contract takes `AgreesOnPage before after page` as a premise.
It compares optional bytes at each offset in the requested half-open page
interval. The bounded read-write backing supplies that premise for two
operations on the page's open handle. Both start from a complete page in
the old file and preserve the mode observed through that handle.
[Cache hit contract](sqlite-vfs-cache-hit.md) ·
[Public statements](../../Silmaril/Machine/SqliteVfs/PageRead/MutationFrame/Thms.lean)

- `write_preserves_page` applies to a successful write. If the write ends at
  or before the page start, or starts at or after the page end, every byte
  in the old page is preserved. The second branch also covers a write
  beyond EOF with zero-filling between the old file and the new bytes.
- `truncate_preserves_page` applies to a successful truncate whose requested
  length is at least the page's exclusive endpoint. The prefix through
  the page survives both a shrink and an extension.

The hypotheses concern one successful call and one page on the same
backing. The proof reads the successful state transition from the existing
`BoundedWriteLaw` for the concrete read-write handler. It places no
constraint on other bytes or on the total file length. Native writer behavior,
dirty data, concurrent handles, transactions and cache invalidation are
outside the model. [Bounded VFS](sqlite-vfs.md)

```sh
lake build --wfail +Silmaril.Machine.SqliteVfs.PageRead.MutationFrame.Checks
make check CHECK_TARGETS=+Silmaril.Machine.SqliteVfs.PageRead.MutationFrame.Checks
```

The kernel checks a write ending at the page start, a write beyond EOF, and
a truncate exactly to the page end. A successful overlapping write changes
a page byte and falsifies agreement. The check module prints the transitive
axioms of the two public theorems.
[Kernel fixtures](../../Silmaril/Machine/SqliteVfs/PageRead/MutationFrame/Checks.lean)
