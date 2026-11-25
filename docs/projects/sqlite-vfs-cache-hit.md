# SQLite cache hit versus read-only refetch

`CacheHit.lookup` checks one slot for the same handle generation, page
number and page size. An absent, vacant, or mismatched slot yields no
bytes. A hit is a pure observation and emits no VFS exchange.
[Definitions](../../Silmaril/Machine/SqliteVfs/PageRead/CacheHit/Defs.lean)

`hit_after_fill_matches_refetch` starts from a caller-owned vacant slot and
an admitted page address on a live handle. The page must fit the original
file. The lookup sees the cache produced by the original read-only fill.
The reference operation starts from the same vacant input slot and refetches
against the current file, where the same handle must be live. For each offset
in the requested half-open interval, the original and current snapshots
must have the same optional byte. The proof derives that the current read
still fits. Bytes outside the interval and full file lengths may differ.
The reference outcome contains exactly one successful exchange with the
same bytes as the hit, preserves its file state, and installs the page.
[Public theorems](../../Silmaril/Machine/SqliteVfs/PageRead/CacheHit/Thms.lean)

`runHit_matches_refetch` additionally proves the VFS trace of the reference
operation is valid. The cache and VFS branches give the same complete
optional VDBE result for every shared base, database and root, program, fuel
bound, and initial state. A page miss, a supplied page with a rejected leaf
or record, and an accepted empty leaf have distinct outcomes.
[Designated-root VDBE](sqlite-vfs-vdbe-leaf.md)

The theorem concerns one slot from one identified successful fill. The
caller establishes byte agreement for that operation. General cache
coherence, mutation or eviction algorithms, concurrent SQLite, and
multi-page traversal are outside the model.

```sh
lake build --wfail +Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Checks
make check CHECK_TARGETS=+Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Checks
```

Fixtures cover different bytes and length outside the read interval, a
stale handle lookup, an exact typed row, a malformed record, and a valid
empty leaf. An in-range value change gives different rows when the
byte-agreement premise is absent. The larger parser and VM fixtures use
test-only evaluator imports. The general theorem proofs use ordinary
imports and are kernel checked.
[Checks](../../Silmaril/Machine/SqliteVfs/PageRead/CacheHit/Checks.lean)
