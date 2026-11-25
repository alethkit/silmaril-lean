#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 ]]; then
  echo "usage: $0 QUOTED_SQLITEWASM_DIR" >&2
  exit 2
fi
src=$(realpath "$1")
root=$(dirname "$src")
tool=$(dirname "$(realpath "$0")")
cd "$tool/../../.."

if [[ $(basename "$src") != SqliteWasm || ! -f "$src/WholeModule.olean" ]]; then
  echo 'build the whole-module decoder in this generated SqliteWasm directory first' >&2
  exit 2
fi

bash tools/sqlite-wasm/prepared-invocation/check.sh "$src"
cp "$tool/PreparedInitReentry.lean" "$src/"
cp "$tool/ImportCheck.lean" "$src/PreparedInitReentryImportCheck.lean"

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
flags=(-j1 -s 131072 -M 6144 -DautoImplicit=false -E warning --root="$root")
lake env /usr/bin/time -f 'PreparedInitReentry: %e s wall, %M KiB peak RSS' \
  lean "${flags[@]}" -o "$src/PreparedInitReentry.olean" "$src/PreparedInitReentry.lean"
lake env /usr/bin/time -f 'Ordinary original-byte import: %e s wall, %M KiB peak RSS' \
  lean "${flags[@]}" "$src/PreparedInitReentryImportCheck.lean"
