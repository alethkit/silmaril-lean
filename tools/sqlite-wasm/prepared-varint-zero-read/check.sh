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

bash tools/sqlite-wasm/prepared-varint-reader/check.sh "$src"
cp "$tool/PreparedVarintZeroRead.lean" "$src/"
cp "$tool/ImportCheck.lean" "$src/PreparedVarintZeroReadImportCheck.lean"
export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
flags=(-j1 -s 131072 -M 6144 -DautoImplicit=false -E warning --root="$root")
lake env /usr/bin/time -f 'PreparedVarintZeroRead: %e s wall, %M KiB peak RSS'   lean "${flags[@]}" -o "$src/PreparedVarintZeroRead.olean" "$src/PreparedVarintZeroRead.lean"
lake env /usr/bin/time -f 'Ordinary import and fixed-address replay: %e s wall, %M KiB peak RSS'   lean "${flags[@]}" "$src/PreparedVarintZeroReadImportCheck.lean"
