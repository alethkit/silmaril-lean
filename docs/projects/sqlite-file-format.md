# SQLite file and record readers

This slice parses SQLite database headers and page views, decodes SQLite
varints, and reads records with raw storage classes. The raw reader
distinguishes TEXT octets from BLOB octets, including malformed Unicode.
The decoded reader uses the file's declared encoding for TEXT. File
bounds, varint consumption, and selected storage-class laws are checked
in Lean. File parsing here is separate from B-tree traversal and SQL.

The Lean definitions and proofs are by Jad-Elkhaleq Ghalayini (also
credited as Jad Ghalayini), distributed under this repository's MIT
license. They follow SQLite's public-domain format documentation.
The inspected Docsrc file was `pages/fileformat2.in` at
`c6b42ef8f433261b89110e6a6229b213921b7ea791ee3b53d88c02cf773c92fd`,
SHA-256 `44f562c28dc226eeb54cb68daca5328dbf163d2c6ac901b32ff4bd88db7b0bfa`.
[SQLite file format](https://sqlite.org/fileformat2.html) ·
[SQLite copyright](https://sqlite.org/copyright.html)

```sh
make check CHECK_TARGETS=sqlite_file_format_compatibility
```

The test executable reads fresh 512-byte-page UTF-8, UTF-16LE and UTF-16BE
databases generated with the pinned Linux x86-64 SQLite 3.54.1 corpus
binary. It checks headers, signed rowids, raw bytes, interpreted records,
malformed inputs and fixture preservation. The test covers a controlled
table leaf. [Oracle provenance](../../corpus/sqlite/package.toml)
