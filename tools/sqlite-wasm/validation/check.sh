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

if [[ $(basename "$src") != SqliteWasm || ! -f "$src/WholeModule.olean" ]]; then
  echo 'build the whole-module fixture in the generated SqliteWasm directory first' >&2
  exit 2
fi

/usr/bin/time -f 'validator prerequisites: %e s wall, %M KiB peak RSS' \
  timeout 300 lake build --wfail +Silmaril.Wasm.Validation.Check.Validate
cp "$tool"/{ValidationInputs,ValidationEvidence,ReactorValidation}.lean "$src/"
cp "$tool/ImportCheck.lean" "$src/ValidationImportCheck.lean"

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
for name in ValidationInputs ValidationEvidence ReactorValidation ValidationImportCheck; do
  file="$src/$name.lean"
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" \
    timeout 120 lean -j1 -s 131072 -M 6144 -DautoImplicit=false -DwarningAsError=true \
    --root="$root" -o "${file%.lean}.olean" "$file"
done
