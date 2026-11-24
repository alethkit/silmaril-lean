#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 ]]; then
  echo 'usage: build.sh WORK_DIR' >&2
  exit 2
fi

tool=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$tool/../.." && pwd)
source "$tool/pins.sh"
mkdir -p "$1/downloads"
work=$(cd "$1" && pwd)
tmp=$(mktemp -d "$work/build.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

archive=$work/downloads/$sdk.tar.gz
fetch "$sdk_url" "$sdk_sha" "$archive"
tar -xzf "$archive" -C "$tmp"

cd "$repo/corpus/sqlite"
sha256sum --check upstream.sha256
cd upstream/sqlite-amalgamation-3540100
"$tmp/$sdk/bin/clang" --version
"$tmp/$sdk/bin/clang" --target=wasm32-wasip1 -O2 \
  -DSQLITE_WASI=1 -DSQLITE_THREADSAFE=0 -DSQLITE_OMIT_LOAD_EXTENSION=1 \
  -DSQLITE_NOHAVE_SYSTEM -DSQLITE_OMIT_WAL=1 \
  -D_WASI_EMULATED_SIGNAL -D_WASI_EMULATED_PROCESS_CLOCKS -D_WASI_EMULATED_GETPID \
  -Wl,-z,stack-size=1048576 -Wl,--strip-all \
  -o "$tmp/sqlite3.wasm" shell.c sqlite3.c \
  -lwasi-emulated-signal -lwasi-emulated-process-clocks -lwasi-emulated-getpid -lm
check_sha "$shell_sha" "$tmp/sqlite3.wasm"
mv -f -- "$tmp/sqlite3.wasm" "$work/sqlite3.wasm"
