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
      ! -f "$src/WholeModule.olean" || ! -f "$src/ArtifactCheck.olean" ]]; then
  echo 'build the whole-module decoder and artifact checks in this generated SqliteWasm directory first' >&2
  exit 2
fi

bash tools/sqlite-wasm/direct-preparation/check.sh "$src"
lake build --wfail +Silmaril.Wasm.Link.Preparation +Silmaril.Wasm.Verify.Kernel.Defs
cp "$tool/PreparedFreeNull.lean" "$src/"
cp "$tool/ImportCheck.lean" "$src/PreparedFreeNullImportCheck.lean"

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
flags=(-j1 -s 131072 -M 6144 -DautoImplicit=false -E warning --root="$root")
for name in PreparedFreeNull PreparedFreeNullImportCheck; do
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" \
    lean "${flags[@]}" -o "$src/$name.olean" "$src/$name.lean"
done
