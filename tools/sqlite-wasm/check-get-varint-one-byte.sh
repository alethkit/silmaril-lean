#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo "usage: $0 ARCHIVE_DIR WORK_DIR" >&2
  exit 2
fi
tool=$(dirname "$(realpath "$0")")
bash "$tool/check.sh" "$@"

root="$(realpath "$2")/lean"
src="$root/SqliteWasm"
cp "$tool"/{GetVarintOneByte,GetVarintOneByteImport}.lean "$src/"
cd "$tool/../.."
lake build --wfail +Silmaril.Wasm.Logic.Memory.Thms +Silmaril.Wasm.Execution.Core.Instantiation
export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
flags=(-j1 -s 131072 -DautoImplicit=false -E warning --root="$root")
lake env /usr/bin/time -f '%e s wall, %M KiB peak RSS' lean "${flags[@]}" \
  -o "$src/GetVarintOneByte.olean" "$src/GetVarintOneByte.lean"
lake env lean "${flags[@]}" "$src/GetVarintOneByteImport.lean"
