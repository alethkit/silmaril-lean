# Checked SQLite file images

```sh
lake build --wfail sqlite_image_lean sqlite_lean
.lake/build/bin/sqlite_image_lean sample.sqlite -7 100 4 -91
.lake/build/bin/sqlite_lean --immutable sample.sqlite \
  'SELECT id,amount FROM sample ORDER BY id;'
```

The writer accepts explicit pairs of signed 64-bit rowids and amounts.
The output is a new 1024-byte SQLite file with one STRICT
`sample(id INTEGER PRIMARY KEY, amount INTEGER NOT NULL)` table. It
rejects duplicate rowids, malformed or out-of-range arguments and inputs
that exceed one leaf's byte capacity. For one-byte rowids, 33 rows fit
and 34 do not. Images with wider rowid encodings reach capacity sooner.

The file header, fixed-width integer records, and packed leaf layout have
separate definitions. The amount uses serial type 6 and the rowid alias
uses the serialized NULL placeholder. The catalogue occupies page 1 and
the data occupies page 2. Encoding finishes before the tool opens the
output. It uses exclusive creation and flushes the handle. An I/O error
after creating the file can leave a partial file.

The Lean theorem for an accepted image proves that it is exactly two
512-byte pages and that the file reader reconstructs the snapshot's
ordered VM entries. The logical write profile accepts INSERT, UPDATE
and DELETE over typed snapshots with explicit duplicate and NOT NULL
errors, statement failure preservation, commit and rollback. The CLI
populates a fresh snapshot. A caller can also pass a committed snapshot
to the pure checked image function.

Routine tests reopen the Lean-written files with pinned SQLite 3.54.1,
check `integrity_check` and STRICT metadata, and compare ordered values
with the Lean shell. They cover empty images, signed limits, the
one-byte-rowid capacity boundary, malformed alias cells, rejection
without opening a destination, and preservation of existing files.
They also run the logical write differential on 17 snapshots.

This profile has one leaf per tree and constructs fresh images. Page
splitting, changes to an existing SQLite image, journaling, recovery,
durability and concurrent access require separate models. The logical
and encoder foundations are by Jad-Elkhaleq Ghalayini and are distributed
under this repository's MIT license. [SQLite file format](https://sqlite.org/fileformat2.html) ·
[Pinned native oracle](../../corpus/sqlite/package.toml)

```sh
make check CHECK_TARGETS='sqlite_lean sqlite_image_lean'
```
