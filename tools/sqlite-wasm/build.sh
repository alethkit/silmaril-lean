#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo "usage: $0 ARCHIVE_DIR OUTPUT.wasm" >&2
  exit 2
fi
archives=$(realpath "$1")
output=$(realpath -m "$2")
manifest=$(dirname "$(realpath "$0")")/artifact.sha256
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

(
  cd "$archives"
  sha256sum --check <<'HASHES'
0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9  sqlite-amalgamation-3540100.zip
0507679dff16814b74516cd969a9b16d2ced1347388024bc7966264648c78bfb  wasi-sdk-30.0-x86_64-linux.tar.gz
HASHES
)
unzip -q "$archives/sqlite-amalgamation-3540100.zip" -d "$tmp"
tar -xzf "$archives/wasi-sdk-30.0-x86_64-linux.tar.gz" -C "$tmp"
(
  cd "$tmp"
  sha256sum --check <<'HASHES'
0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52  sqlite-amalgamation-3540100/sqlite3.c
a5431c3533853c135005e2d6e32b211e7921c9255e69f34d5557a319c24a6169  wasi-sdk-30.0-x86_64-linux/bin/clang
57ca1189824aed3afefcbecb778ca5f0f0a7a7f0abf3666940275b94b9435e7d  wasi-sdk-30.0-x86_64-linux/bin/wasm-ld
HASHES
  wasi-sdk-30.0-x86_64-linux/bin/clang \
    -Os -mexec-model=reactor \
    -DSQLITE_THREADSAFE=0 -DSQLITE_OMIT_LOAD_EXTENSION -DSQLITE_OMIT_WAL -DSQLITE_TEMP_STORE=3 \
    -Wl,--strip-all -Wl,--export=sqlite3_libversion_number \
    -Wl,--export=sqlite3_open -Wl,--export=sqlite3_prepare_v2 -Wl,--export=sqlite3_step \
    -Wl,--export=sqlite3_column_int -Wl,--export=sqlite3_finalize -Wl,--export=sqlite3_close \
    -Wl,--export=malloc -Wl,--export=free sqlite-amalgamation-3540100/sqlite3.c -o sqlite3.wasm
  sha256sum --check "$manifest"
)
install -m 0644 "$tmp/sqlite3.wasm" "$output"
