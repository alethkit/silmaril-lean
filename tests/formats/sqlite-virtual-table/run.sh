#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."

lake=${LAKE:-lake}
upstream=corpus/sqlite/upstream/sqlite-amalgamation-3540100
test_dir=tests/formats/sqlite-virtual-table
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

"$lake" build --wfail +Silmaril.Formats.Sqlite.VirtualTable.Backed.Thms
"$lake" env lean -DautoImplicit=false -DwarningAsError=true "$test_dir/Axioms.lean"
if ! "$lake" env lean -DautoImplicit=false -DwarningAsError=true --run "$test_dir/Regression.lean" > "$tmp/lean"; then
  cat "$tmp/lean"
  exit 1
fi

# Check the pinned inputs used by this probe, then compile upstream separately.
(cd corpus/sqlite && awk '/sqlite3\.[ch]$/ {print}' upstream.sha256 | sha256sum -c -)
"${CC:-cc}" -O1 -DSQLITE_THREADSAFE=1 -c "$upstream/sqlite3.c" -o "$tmp/sqlite3.o"
"${CC:-cc}" -std=c11 -Wall -Wextra -Werror -O2 -I "$upstream" "$test_dir/native.c" \
  "$tmp/sqlite3.o" -pthread -ldl -lm -o "$tmp/probe"
"$tmp/probe" > "$tmp/native"
diff -u "$tmp/lean" "$tmp/native"
echo "SQLite 3.54.1 virtual-table cursor traces and SQL rows agree on $(grep -c '^case ' "$tmp/native") queries"
