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

if [[ $(basename "$src") != SqliteWasm ]]; then
  echo 'expected the generated SqliteWasm directory from the reactor quotation' >&2
  exit 2
fi
for dependency in AllFunctionVectors MetadataVectors SmallSections DataSection DataIndices; do
  if [[ ! -f "$src/$dependency.olean" ]]; then
    echo "missing $dependency.olean, see whole-module/README.md for fixture setup" >&2
    exit 2
  fi
done

cp "$tool"/{WholeModuleEvidence,WholeModule}.lean "$src/"
cp "$tool/ImportCheck.lean" "$src/WholeModuleImportCheck.lean"

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
for name in WholeModuleEvidence WholeModule WholeModuleImportCheck; do
  file="$src/$name.lean"
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" lean -j1 -s 131072 -M 6144 \
    -DautoImplicit=false -DwarningAsError=true --root="$root" -o "${file%.lean}.olean" "$file"
done
