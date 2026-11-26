# SQLite global object state

Import `Silmaril.Machine.SQLite.GlobalState.Store.Allocator.Thms` for the
allocator-inclusive store, or `Silmaril.Machine.SQLite.GlobalState.Store.Thms`
for object histories, checked projections, the kind store and the VFS roots.
This layer sits beside `Silmaril.Machine.SQLite.Architecture.All` and uses the
boundaries in the [Track E coverage inventory at `9aeb8467`][coverage].

## Object store

`ObjectStore ObjectId` uses `Std.ExtHashMap` with caller-supplied identities.
Its operations use lawful boolean equality and hashing. A successful `lookup`
reports the one recorded `ObjectKind`. `insert` replaces the binding and
`erase` removes it. In namespace `ObjectStore`, `lookup_empty` covers absence
in `empty`. `lookup_insert_self` and `lookup_erase_self` describe the edited
identity. `lookup_insert_of_ne` and `lookup_erase_of_ne` give the frame at
every other identity. `ext` identifies stores with the same lookups. `HasKind`
expresses a successful classification, `hasKind_unique` checks uniqueness,
and `Ref` packages classification evidence for one snapshot. Map edits are
mathematical operations. The kind store records present objects and carries
no allocation history.

The kind names refer to these SQLite 3.54.1 objects.

| Kind | Source object |
| --- | --- |
| `connection`, `statement` | `sqlite3` and `sqlite3_stmt` (implemented by `Vdbe`). [C API][api] · [VDBE API][vdbeapi] |
| `blob`, `backup` | `sqlite3_blob` (implemented by `Incrblob`) and `sqlite3_backup`. [Incremental blob][blob] · [Backup][backup] |
| `vfs`, `file` | `sqlite3_vfs` and `sqlite3_file`, the latter representing a file handle. [C API][api] |
| `pageCache`, `pager` | The Pager-facing `PCache` and `Pager`. `PCache` uses a pluggable `sqlite3_pcache` internally. [Page cache][cache] · [Pager][pager] |
| `btree` | `Btree`, the connection's handle to `BtShared` content. [B-tree structures][btree] |

`VfsRoots` holds the ordered distinct VFS references registered in one store
snapshot. `defaultVfs` is the head of that list, or `none` when it is empty.
SQLite's `sqlite3_vfs_find(NULL)` reads that head after initialization; a
named lookup scans for a matching name. A connection's selected VFS is an
object link established during open. Name resolution, registration transitions
and the lifetime of a selected VFS across unregistration remain to be modeled.
[Registry][os] · [Connection open][main]

## Finite snapshots and erasure

`Objects ObjectId Payload` and `History ObjectId Payload` are finite
`Std.ExtHashMap` snapshots keyed by the same abstract identities as
`ObjectStore`. Each present `Object Payload` carries its kind, its
`PresentState`, and a value of `Payload kind`. The kind-indexed family
can also be constant. `toStates` instantiates it with `Unit`, giving
`StateStore` or `StateHistory`. `Objects.toKinds` erases the state and
payload into the existing objects-only `ObjectStore`.

| Snapshot status | `History.lookup` | `History.toObjects.lookup` |
| --- | --- | --- |
| Allocated, in the ordinary open or live state | `some (.present object)` with state `.live` | `some object` |
| Zombie, still present | `some (.present object)` with state `.zombie` | `some object` |
| Freed, with allocated kind retained | `some (.freed kind)` | `none` |
| Never bound in this history | `none` | `none` |

`live` describes ordinary presence at this abstraction level. For
example, a live file object still needs the relevant open mode and access
grant in a file operation contract. `lookupLive` restricts the observation
to live objects. SQLite's `sqlite3_close_v2` can leave a connection
allocated as a zombie until its outstanding statements, BLOB handles and
backups are released. This motivates the separate state. Which snapshots
are reachable, including which kinds a resource contract can mark zombie,
is left to that contract. A nullable reference can be an `Option ObjectId`
in the payload. Its `none` records a null field inside a present object.
[Close API][close] · [Zombie disposal][main]

`History.allocate` requires `Fresh` (a missing history binding) and records
a live object. `History.free` requires a present object and replaces its
record with a tombstone. `fresh_allocate_iff` removes just the allocated ID
from the fresh IDs and `fresh_free_iff` preserves freshness at every ID.
Together these prevent reuse across these edits on a retained history.
`History.updatePresent` requires evidence of the current present entry.
Its new state and payload replace that entry at the same ID, with the payload
typed at the current kind. A live entry can become a zombie and remain in
the present view. The operation accepts either present state as input and
output. The contract supplies allowed lifecycle changes and permissions.
`lookup_updatePresent_self` gives the exact new entry, all three edit
operations have `lookup_*_of_ne` frame laws, and
`fresh_updatePresent_iff` preserves freshness at every ID.
`toObjects_free` equates forgetting a tombstone with deleting the binding
in the objects-only snapshot. `toObjects_not_injective` exhibits the
obstruction to reversing that erasure. The same objects can come from a
history with a tombstone or one where the ID was never bound. These edits
are operations on finite maps. Resource families, address reuse, and
SQLite API transitions belong to subsequent resource contracts.

## Raw blocks and object visibility

`AllocatorStore ObjectId AllocId Payload Live Tombstone` combines an object
`History` with a separate `AllocationHistory AllocId Live Tombstone`.
An allocation lookup returns `some (.live metadata)`, `some (.freed metadata)`,
or `none` for an ID never issued in that history. The last case defines
`AllocationHistory.Fresh`. The live and tombstone metadata types are
parameters. The resource contract can supply allocation family, requested
and usable sizes, and ownership rules. The raw table has pointwise lookup
laws for an empty table and insertion at the edited or any other ID.
The C API allows `sqlite3_msize` to report more bytes than originally requested
and permits memory to be reused after `sqlite3_free`. A contract that
models address reuse can use allocation identities with a generation.
[Allocation API][allocation-api]

`StoreId.object` and `StoreId.allocation` select distinct identity spaces
even when the ID types and underlying values coincide. Object visibility
comes from a present object entry. It carries no assertion about which
allocator block provides storage. For example, `sqlite3PagerOpen` lays
out a `Pager`, `PCache` and file-handle storage in a single allocation.
An object ID for each visible instance does not imply a separate allocation
for each portion. A resource contract can relate multiple objects to one
block and express any offset or ownership facts it needs. [Pager layout][pager-layout]

`AllocatorStore.lookup_toObjects` gives the tagged erasure law. It preserves
present objects, including zombies, and erases object tombstones and all
raw blocks. `checkObjectId` passes object-tagged IDs to the component view's
checked admission. `checkObjectId_allocation` proves that an allocation tag
cannot supply a checked object ID. The check suite covers both lookups at
coincident numeric IDs and a live-to-zombie update with a null payload field.

## Checked component views

`KindView.supports` defines four filters. Each keeps the original IDs of
all present objects whose kind it supports.

| View | Included kinds | Source rationale |
| --- | --- | --- |
| `.vfs` | `vfs`, `file` | The VFS registry and OS-interface file-handle ABI. [Registry][os] · [C API][api] |
| `.publicHandles` | `connection`, `statement`, `blob`, `backup` | Opaque database-operation handles in the C API. [C API][api] |
| `.cache` | `pageCache`, `pager`, `file` | Pager manages its `PCache` with file handles for its database and journals. [Pager][pager] · [Page cache][cache] |
| `.btree` | `btree`, `pager` | The B-tree handle reaches its backing Pager through `BtShared`. [B-tree structures][btree] |

The VFS and cache policies share `file`. The cache and B-tree policies
share `pager`. The public-handle policy covers database operations, while
the VFS extension ABI has its own view. The filters are kind policies for
whole snapshots. Exact reachability from a registered VFS, a particular
connection, a B-tree, or a cache requires roots and object links. For
example, the VFS filter admits an unregistered VFS and the cache filter admits
files unrelated to any given Pager. `PCache` identifies the cache object,
while Track E's `PageRead.Cache` observes page slots.

`lookup_toObjects`, `lookup_map`, `lookup_toKinds` and `lookup_restrict`
give the pointwise erasures and filters. `toObjects_map` commutes forgetting
the history with kind-indexed payload mapping. `map_restrict` commutes
that mapping with the view filter. `toKinds_map` preserves kinds through
payload mapping, and `toKinds_restrict` commutes erasing to kinds with
restricting the view.

For a fixed finite `Objects` snapshot and a `KindView`, `PresentId` is
the subtype of IDs with a successful supported lookup. It includes zombies.
`checkId` tests membership for a raw ID, and `get` is total on that
subtype. `checkId_isSome` agrees with the projected kind map on admission.
`lookup_get` and `lookup_kind_get` agree with the source object and
projected kind, respectively. These laws cover the supported present
carrier of the given snapshot.

## Boundaries for later increments

- Use the `Object` payload family for source struct fields. A later per-kind
  store can recover or refine the indexed payload at the required kind.
  Frame laws for updates to new fields and preservation of root references
  are obligations when moving between snapshots.
- Reuse `Interface.Connection`, `Session` and `Prepared` for D3 observations.
  Relate a file identity to `VFS.Opened` through its path and backing-local
  generation. `VFS.FileMap` observes backing by path, and `PageRead.Cache`
  observes slots. A `Pager.LockGrant` describes caller-supplied access.
  B-tree lookup observes a designated decoded page in the existing profile.
  Keep these as component-specific views with explicit adapter premises.
- Write resource contracts when operations introduce lifetimes. Distinguish
  store presence from owning, borrowing, or retaining an object. The
  statement's connection, blob's supporting statement, backup's source and
  destination, shared B-tree content and VFS references held after open need
  their own validity and release rules. The map's frame laws alone give no
  preservation guarantee for those relationships.

## Replay

```bash
root=Silmaril.Machine.SQLite.GlobalState
lake build --wfail +"$root".Checks +"$root".Store.Checks +"$root".Store.Allocator.Checks
for check in Checks Store/Checks Store/Allocator/Checks; do
  lake env lean -DautoImplicit=false -DwarningAsError=true \
    "Silmaril/Machine/SQLite/GlobalState/$check.lean" || exit 1
done
for module in "$root".{Defs,Roots,Thms,Checks,Store.Defs,Store.Thms,Store.Checks} \
    "$root".Store.Allocator.{Defs,Thms,Checks} \
    Silmaril.Proofs.Machine.SQLite.GlobalState.Store.Erasure; do
  SILMARIL_REPLAY_MODULE="$module" \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean || exit 1
done
```

The check modules print the public theorem axiom dependencies for comparison
with [the axiom policy](../../../policy.toml). The store checks exercise the
two policy overlaps, checked admission, a zombie with a null payload field,
and a freed ID versus a never-bound ID.

[coverage]: https://github.com/hiloopai/silmaril-lean/blob/9aeb8467ad1e1f962f9f166965e9fabc4e7e03b4/docs/projects/sqlite-track-e/coverage-v1.md
[api]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in
[close]: https://www.sqlite.org/c3ref/close.html
[allocation-api]: https://www.sqlite.org/c3ref/free.html
[pager-layout]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L4924-L4951
[vdbeapi]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeapi.c
[blob]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeblob.c
[backup]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/backup.c
[cache]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pcache.c
[pager]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c
[btree]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btreeInt.h
[os]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.c
[main]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c
