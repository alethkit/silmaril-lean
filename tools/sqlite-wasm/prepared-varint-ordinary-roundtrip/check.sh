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

if [[ $(basename "$src") != SqliteWasm || ! -f "$src/WholeModule.olean" ||
      ! -f "$src/GetVarint.olean" || ! -f "$src/OrdinaryVarintHelper.olean" ]]; then
  echo 'build the whole-module, successful-reader and writer checks in this generated SqliteWasm directory first' >&2
  exit 2
fi

bash tools/sqlite-wasm/direct-preparation/check.sh "$src"
lake build --wfail +Silmaril.Wasm.Link.Preparation +Silmaril.Formats.Sqlite.Varint.Normal.Thms
cp "$tool/PreparedVarintOrdinaryRoundtrip.lean" "$src/"
cp "$tool/ImportCheck.lean" "$src/PreparedVarintOrdinaryRoundtripImportCheck.lean"
export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
flags=(-j1 -s 131072 -M 6144 -DautoImplicit=false -E warning --root="$root")
lake env /usr/bin/time -f 'PreparedVarintOrdinaryRoundtrip: %e s wall, %M KiB peak RSS' \
  lean "${flags[@]}" -o "$src/PreparedVarintOrdinaryRoundtrip.olean" "$src/PreparedVarintOrdinaryRoundtrip.lean"
lake env /usr/bin/time -f 'Ordinary import and three replays: %e s wall, %M KiB peak RSS' \
  lean "${flags[@]}" "$src/PreparedVarintOrdinaryRoundtripImportCheck.lean"
