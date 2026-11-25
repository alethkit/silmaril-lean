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

bash tools/sqlite-wasm/prepared-invocation/check.sh "$src"
bash tools/sqlite-wasm/prepared-version-export/check.sh "$src"
cp "$tool/PreparedInitVersion.lean" "$src/"
cp "$tool/ImportCheck.lean" "$src/PreparedInitVersionImportCheck.lean"
cp "$tool/Replay.lean" "$src/PreparedInitVersionReplay.lean"

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
flags=(-j1 -s 131072 -M 6144 -DautoImplicit=false -E warning --root="$root")
lake env /usr/bin/time -f 'PreparedInitVersion: %e s wall, %M KiB peak RSS' \
  lean "${flags[@]}" -o "$src/PreparedInitVersion.olean" "$src/PreparedInitVersion.lean"
lake env /usr/bin/time -f 'Original-byte import: %e s wall, %M KiB peak RSS' \
  lean "${flags[@]}" "$src/PreparedInitVersionImportCheck.lean"
lake env /usr/bin/time -f 'Executable sequence replay: %e s wall, %M KiB peak RSS' \
  lean "${flags[@]}" --run "$src/PreparedInitVersionReplay.lean"
