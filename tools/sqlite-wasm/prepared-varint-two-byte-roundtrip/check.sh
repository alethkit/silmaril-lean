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
lake build --wfail +Silmaril.Wasm.Link.Preparation +Silmaril.Formats.Sqlite.Varint.Thms
cp tools/sqlite-wasm/PutVarintTwoByte.lean "$src/"
cp "$tool/PreparedVarintTwoByteRoundtrip.lean" "$src/"
cp "$tool/ImportCheck.lean" "$src/PreparedVarintTwoByteRoundtripImportCheck.lean"
export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
flags=(-j1 -s 131072 -M 6144 -DautoImplicit=false -E warning --root="$root")
for name in PutVarintTwoByte PreparedVarintTwoByteRoundtrip; do
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" lean "${flags[@]}" \
    -o "$src/$name.olean" "$src/$name.lean"
done
lake env /usr/bin/time -f 'Ordinary import and four replays: %e s wall, %M KiB peak RSS' \
  lean "${flags[@]}" "$src/PreparedVarintTwoByteRoundtripImportCheck.lean"
