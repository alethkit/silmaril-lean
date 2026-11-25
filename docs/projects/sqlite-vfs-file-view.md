# SQLite file views over VFS reads

`image_page_trace` relates one existing `Formats.Sqlite.File.Image.page?`
view to the landed read-only VFS backing. The caller supplies equality of the
file's byte list and the image's source snapshot, a live handle, and admission
of that one read range. With `size = image.header.pageSize` and
`offset = (number - 1) * size`, the VFS trace contains exactly one full
read of `[offset, offset + size)`. Its reply has the length of the physical
page view and agrees with that view at every in-range byte. There are no
reads outside that interval. The entire backing state is unchanged.
[Statements](../../Silmaril/Machine/SqliteVfs/FileView/Thms.lean) ·
[File page view](../../Silmaril/Formats/Sqlite/File/Defs.lean)

`image_page_fill` applies the same boundary to the owned page fill. An owned
vacancy is the additional premise. The outcome holds the exact page in the
target slot and retains the singleton VFS exchange. Every other slot keeps its
previous value. The checked example installs bytes from a second-page view
while keeping the first-page resident slot.
[Page fill](sqlite-page-read.md) ·
[Checks](../../Silmaril/Machine/SqliteVfs/FileView/Checks.lean)

A reported view entails the range fits the shared snapshot, so these theorems
take the full-read branch. A truncated file or absent logical page can fail
the premises. The lower VFS may report a short read when a raw range crosses
EOF. The strict page-fill contract leaves the cache unchanged in that case.
This link concerns physical page bytes, including any reserved tail. SQLite
file acquisition, header validity beyond the assumed view, cache freshness,
native pager or C correspondence, and B-tree decoding are outside the proof.
[VFS contract](sqlite-vfs.md)

Run from the repository root with the pinned Lean toolchain.

```sh
lake build --wfail +Silmaril.Machine.SqliteVfs.FileView.Checks
make check CHECK_TARGETS=+Silmaril.Machine.SqliteVfs.FileView.Checks
```

The example uses a two-byte page geometry to check offsets and frame behavior.
It constructs a view directly so the checks depend only on the page-view
contract.
