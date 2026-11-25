#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo "usage: $0 ARCHIVE_DIR WORK_DIR" >&2
  exit 2
fi
tool=$(dirname "$(realpath "$0")")
bash "$tool/check-get-varint-one-byte.sh" "$@"

root="$(realpath "$2")/lean"
src="$root/SqliteWasm"
cp "$tool"/{GetVarintTwoByte,GetVarintTwoByteImport}.lean "$src/"
cd "$tool/../.."
lake build --wfail +Silmaril.Wasm.Auto2.VCGen.Thms
export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
flags=(-j1 -s 131072 -DautoImplicit=false -E warning --root="$root")
lake env /usr/bin/time -f '%e s wall, %M KiB peak RSS' lean "${flags[@]}" \
  -o "$src/GetVarintTwoByte.olean" "$src/GetVarintTwoByte.lean"
lake env /usr/bin/time -f '%e s wall, %M KiB peak RSS' lean "${flags[@]}" \
  "$src/GetVarintTwoByteImport.lean"
