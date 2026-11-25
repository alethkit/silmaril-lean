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

if [[ $(basename "$src") != SqliteWasm || ! -f "$src/ReactorValidation.olean" ]]; then
  echo 'run the reactor validation check in the generated SqliteWasm directory first' >&2
  exit 2
fi

cp "$tool"/{GuardEvidence,ValidationGuards}.lean "$src/"
cp "$tool/ImportCheck.lean" "$src/ValidationGuardsImportCheck.lean"

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
for name in GuardEvidence ValidationGuards ValidationGuardsImportCheck; do
  file="$src/$name.lean"
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" \
    timeout 120 lean -j1 -s 131072 -M 6144 -DautoImplicit=false -DwarningAsError=true \
    --root="$root" -o "${file%.lean}.olean" "$file"
done
