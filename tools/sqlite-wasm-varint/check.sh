#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo "usage: $0 ARCHIVE_DIR WORK_DIR" >&2
  exit 2
fi
archives=$(realpath "$1")
mkdir -p "$2"
work=$(realpath "$2")
tool=$(dirname "$(realpath "$0")")
cd "$tool/../.."

bash tools/sqlite-wasm/build.sh "$archives" "$work/reactor.wasm" "$work/reactor.map"
python3 "$tool/prepare.py" "$work/reactor.wasm" "$work/reactor.map" "$work/test-exports.wasm" |
  tee "$work/functions.json"
lake build --wfail +Silmaril.Formats.Sqlite.Varint.Defs
lake env lean -j1 -DautoImplicit=false -E warning --root="$tool" \
  --run "$tool/Vectors.lean" > "$work/vectors.json"
node "$tool/runtime.mjs" "$work/test-exports.wasm" "$work/vectors.json"
