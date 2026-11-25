# SQLite table-leaf decoding from a VFS page fill

`read_materialized` proves equality between the landed packed table-leaf
reader on a shared `File.View` and on a copy of that entire view. The copy
starts at offset zero in its new source and keeps the view length. The parser
uses the same page-relative base in both calls. For example, a caller uses base
100 on the first page to skip the database header, and base 0 for other leaves.
The theorem covers every base, including out-of-bounds inputs.
[Public statements](../../Silmaril/Machine/SqliteVfs/FileView/TableLeaf/Thms.lean) ·
[Packed table-leaf reader](../../Silmaril/Formats/Sqlite/TableLeaf/Defs.lean)

The proof equates optional byte queries at every local offset, including the
`none` results past the view. Corresponding bounded payload subviews have
equal materialized bytes. These facts preserve the varint reads, fixed-width
header reads, page and cell bounds checks, and packed-cell checks used by
`TableLeaf.read?`. The returned cell list, including its page-relative
cell extents and payloads, agrees exactly. Both runs reject the same inputs.

`image_page_fill_decode` applies that equality to the bytes installed by an
owned VFS page fill. The caller supplies the same file and image snapshot,
an existing physical page view, a live handle, an admitted read interval,
and an owned vacant cache slot. The operation reads exactly one full
physical page at the specified offset and preserves the backing and other
slots. The theorem applies the existing parser to the entire returned page
and compares it with the original page view at the same base. It allows
parser rejection after a successful VFS read.
[File-view contract](sqlite-vfs-file-view.md) · [Owned page fill](sqlite-page-read.md)

This is a result-preservation theorem for the existing parser. It supplies a
boundary to consumers of the packed leaf, such as B-tree row lookup and scan.
General B-tree correctness, file acquisition, cache freshness, mutation,
native pager correspondence, and SQL execution are outside its scope.

```sh
lake build --wfail +Silmaril.Machine.SqliteVfs.FileView.TableLeaf.Checks
make check CHECK_TARGETS=+Silmaril.Machine.SqliteVfs.FileView.TableLeaf.Checks
```

The checks decode a populated 512-byte leaf at a nonzero source offset and
exercise rejection of the same layout with a different page type. The
synthetic fixture contains only a page view. It runs as a Boolean test through
Lean's evaluator and contributes no proof assumptions. The two library
theorems use ordinary imports and kernel-checked proofs. [Checks](../../Silmaril/Machine/SqliteVfs/FileView/TableLeaf/Checks.lean)
