#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 && $# != 3 ]] || [[ ! ${3:-1} =~ ^[1-9][0-9]*$ ]]; then
  echo "usage: $0 INPUT.wasm QUOTED_SQLITEWASM_DIR [JOBS]" >&2
  exit 2
fi
wasm=$(realpath "$1")
src=$(realpath "$2")
root=$(dirname "$src")
jobs=${3:-1}
tool=$(dirname "$(realpath "$0")")
cd "$tool/../.."

if [[ $(basename "$src") != SqliteWasm || ! -f "$src/Object.olean" ]]; then
  echo 'expected a compiled reactor quotation from quote.sh' >&2
  exit 2
fi

# Reuse the reactor's digest check and original byte literal from the selected-record proof.
bash "$tool/check-artifact.sh" "$wasm" "$src"
lake build --wfail +Silmaril.Wasm.Component.ChunkedDecode.Thms
cp "$tool"/{FunctionVector,FunctionPlans,FunctionVectorImport}.lean "$src/"
python3 -B "$tool/generate-function-checks.py" "$src/Original.wasm" "$src" > "$src/function-check-blocks.txt"

export root src LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
compile() {
  local file="$src/$1.lean"
  lake env /usr/bin/time -f "$1: %e s wall, %M KiB peak RSS" lean -j1 -s 131072 -M 6144 \
    -DautoImplicit=false -DwarningAsError=true --root="$root" -o "${file%.lean}.olean" "$file"
}
compile FunctionVector
compile FunctionPlans
export -f compile
xargs -P "$jobs" -n 1 bash -euc 'compile "$1"' bash < "$src/function-check-blocks.txt"
compile FunctionVectorCheck
compile FunctionVectorImport
