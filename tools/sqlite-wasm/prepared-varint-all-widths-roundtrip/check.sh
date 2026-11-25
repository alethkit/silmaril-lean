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

if [[ $(basename "$src") != SqliteWasm ||
      ! -f "$src/WholeModule.olean" || ! -f "$src/GetVarint.olean" ||
      ! -f "$src/PutVarintCheck.olean" || ! -f "$src/PutVarintTwoByte.olean" ||
      ! -f "$src/NineByteVarint.olean" || ! -f "$src/OrdinaryVarintHelper.olean" ]]; then
  echo 'build the whole-module, successful-reader and writer checks in this generated SqliteWasm directory first' >&2
  exit 2
fi

bash tools/sqlite-wasm/direct-preparation/check.sh "$src"
lake build --wfail +Silmaril.Wasm.Link.Preparation \
  +Silmaril.Formats.Sqlite.Varint.Thms +Silmaril.Formats.Sqlite.Varint.Normal.Thms
export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
flags=(-j1 -s 131072 -M 6144 -DautoImplicit=false -E warning --root="$root")

compile() {
  local source=$1
  local name
  name=$(basename "$source" .lean)
  cp "$source" "$src/$name.lean"
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" \
    lean "${flags[@]}" -o "$src/$name.olean" "$src/$name.lean"
}
compile tools/sqlite-wasm/prepared-varint-roundtrip/PreparedVarintRoundtrip.lean
compile tools/sqlite-wasm/prepared-varint-two-byte-roundtrip/PreparedVarintTwoByteRoundtrip.lean
compile tools/sqlite-wasm/prepared-varint-ordinary-roundtrip/PreparedVarintOrdinaryRoundtrip.lean
compile tools/sqlite-wasm/prepared-varint-nine-byte-roundtrip/PreparedVarintNineByteRoundtrip.lean
compile "$tool/PreparedVarintAllWidths.lean"

cp "$tool/ImportCheck.lean" "$src/PreparedVarintAllWidthsImportCheck.lean"
lake env /usr/bin/time -f 'Ordinary original-byte import and endpoint controls: %e s wall, %M KiB peak RSS' \
  lean "${flags[@]}" "$src/PreparedVarintAllWidthsImportCheck.lean"
