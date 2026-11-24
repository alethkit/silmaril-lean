#!/usr/bin/env bash
# Exercise the file and record readers using fresh databases from the pinned C build.
set -euo pipefail
cd "$(dirname "$0")/../../.."

corpus=$PWD/corpus/elf/sqlite/x86_64
(cd "$corpus" && sha256sum -c SHA256SUMS)
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
ln -s "$corpus/libsqlite3.so" "$scratch/libsqlite3.so.0"

for encoding in UTF-8 UTF-16le UTF-16be; do
  file="$scratch/$encoding.sqlite"
  LD_LIBRARY_PATH="$scratch" "$corpus/sqlite3" "$file" "
    PRAGMA page_size=512;
    PRAGMA encoding='$encoding';
    CREATE TABLE sample(flag INTEGER, greeting TEXT, payload BLOB, missing TEXT);
    INSERT INTO sample(rowid,flag,greeting,payload,missing)
      VALUES(9223372036854775807,-129,'Aé',X'00FF',NULL);"
  result=$(LD_LIBRARY_PATH="$scratch" "$corpus/sqlite3" -readonly "$file" "
    SELECT rootpage FROM sqlite_schema WHERE name='sample';
    PRAGMA integrity_check;")
  test "$result" = $'2\nok'
done

sha256sum "$scratch"/UTF-*.sqlite
.lake/build/bin/sqlite_file_format_compatibility \
  "$scratch/UTF-8.sqlite" "$scratch/UTF-16le.sqlite" "$scratch/UTF-16be.sqlite"
