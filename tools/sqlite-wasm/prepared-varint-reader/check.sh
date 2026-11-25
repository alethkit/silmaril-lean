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

if [[ $(basename "$src") != SqliteWasm || ! -f "$src/WholeModule.olean" || ! -f "$src/GetVarint.olean" ]]; then
  echo 'build the whole-module and successful-reader checks in this generated SqliteWasm directory first' >&2
  exit 2
fi

bash tools/sqlite-wasm/direct-preparation/check.sh "$src"
lake build --wfail +Silmaril.Wasm.Link.Preparation
cp "$tool/PreparedVarintReader.lean" "$src/"
cp "$tool/ImportCheck.lean" "$src/PreparedVarintReaderImportCheck.lean"
export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
flags=(-j1 -s 131072 -M 6144 -DautoImplicit=false -E warning --root="$root")
lake env /usr/bin/time -f 'PreparedVarintReader: %e s wall, %M KiB peak RSS'   lean "${flags[@]}" -o "$src/PreparedVarintReader.olean" "$src/PreparedVarintReader.lean"
lake env /usr/bin/time -f 'Ordinary import: %e s wall, %M KiB peak RSS'   lean "${flags[@]}" "$src/PreparedVarintReaderImportCheck.lean"
