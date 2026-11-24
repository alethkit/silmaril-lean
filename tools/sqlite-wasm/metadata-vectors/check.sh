#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo "usage: $0 INPUT.wasm QUOTED_SQLITEWASM_DIR" >&2
  exit 2
fi
wasm=$(realpath "$1")
src=$(realpath "$2")
root=$(dirname "$src")
tool=$(dirname "$(realpath "$0")")
cd "$tool/../../.."

if [[ $(basename "$src") != SqliteWasm || ! -f "$src/Object.olean" ]]; then
  echo 'expected a compiled reactor quotation from quote.sh' >&2
  exit 2
fi

bash "$tool/../check-artifact.sh" "$wasm" "$src"
lake build --wfail +Silmaril.Wasm.Component.ChunkedDecode.Thms
cp "$tool"/{SectionRuns,VectorEvidence,MetadataVectors}.lean "$src/"
cp "$tool/ImportCheck.lean" "$src/MetadataImportCheck.lean"

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
for name in SectionRuns VectorEvidence MetadataVectors MetadataImportCheck; do
  file="$src/$name.lean"
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" lean -j1 -s 131072 -M 6144 \
    -DautoImplicit=false -DwarningAsError=true --root="$root" -o "${file%.lean}.olean" "$file"
done
