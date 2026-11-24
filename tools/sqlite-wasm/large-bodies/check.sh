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
cd "$tool/../../.."

if [[ $(basename "$src") != SqliteWasm || ! -f "$src/Object.olean" ]]; then
  echo 'expected a compiled reactor quotation from quote.sh' >&2
  exit 2
fi

bash "$tool/../check-artifact.sh" "$wasm" "$src"
lake build --wfail +Silmaril.Wasm.Component.ChunkedDecode.Thms
cp "$tool/../FunctionVector.lean" "$src/"
cp "$tool"/{BodyComposition,LargeBodies,ImportCheck}.lean "$src/"

export root src LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
compile() {
  local file="$src/$1.lean"
  lake env /usr/bin/time -f "$1: %e s wall, %M KiB peak RSS" lean -j1 -s 131072 -M 6144 \
    -DautoImplicit=false -DwarningAsError=true --root="$root" -o "${file%.lean}.olean" "$file"
}
compile FunctionVector
compile BodyComposition
lake env lean -j1 -DautoImplicit=false -DwarningAsError=true --run \
  "$tool/Generate.lean" "$src/Original.wasm" "$src" > "$src/large-body-modules.txt"
export -f compile
xargs -P "$jobs" -n 1 bash -euc 'compile "$1"' bash < "$src/large-body-modules.txt"
compile LargeBodies
compile ImportCheck
