# SQLite global object state

Import `Silmaril.Machine.SQLite.GlobalState.Thms` for the kind store, its
lookup laws and the VFS roots. This is a separate layer beside the components
exposed by `Silmaril.Machine.SQLite.Architecture.All`. The starting boundaries
are those in the [Track E coverage inventory at `9aeb8467`][coverage].

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
mathematical operations. Allocators, pointer representations, identity reuse
and object lifetime are outside this model.

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

## Boundaries for later increments

- Put state or struct payloads behind kind-specific lookups when a component
  needs fields. For an indexed store, prove that erasing payloads preserves
  each lookup in the kind store. Prove frame laws for updates to the new fields
  and preserve root references explicitly when moving between snapshots.
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
lake build --wfail +"$root".Checks
lake env lean -DautoImplicit=false -DwarningAsError=true \
  Silmaril/Machine/SQLite/GlobalState/Checks.lean
for part in Defs Roots Thms Checks; do
  SILMARIL_REPLAY_MODULE="$root.$part" \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean || exit 1
done
```

[coverage]: https://github.com/hiloopai/silmaril-lean/blob/9aeb8467ad1e1f962f9f166965e9fabc4e7e03b4/docs/projects/sqlite-track-e/coverage-v1.md
[api]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in
[vdbeapi]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeapi.c
[blob]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeblob.c
[backup]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/backup.c
[cache]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pcache.c
[pager]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c
[btree]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btreeInt.h
[os]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.c
[main]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c
