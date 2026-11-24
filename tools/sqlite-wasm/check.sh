#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo "usage: $0 ARCHIVE_DIR WORK_DIR" >&2
  exit 2
fi
archives=$(realpath "$1")
mkdir -p "$2"
work=$(realpath "$2")
tool=$(dirname "$(realpath "$0")")
cd "$tool/../.."
root="$work/lean"
src="$root/SqliteWasm"
mkdir -p "$src"

bash "$tool/build.sh" "$archives" "$work/sqlite3.wasm"
bash "$tool/quote.sh" "$tool/reactor.json" "$work/sqlite3.wasm" "$src"
bash "$tool/check-artifact.sh" "$work/sqlite3.wasm" "$src"
cp "$tool"/{VersionModel,VersionCheck,PutVarintCheck,Replay}.lean "$src/"
lake build --wfail +Silmaril.Wasm.Binaryen.Exe.Decode \
  +Silmaril.Wasm.Binaryen.Interp +Silmaril.Wasm.ModuleParts.Defs \
  +Silmaril.Wasm.Execution.Core.Properties +Silmaril.Formats.Sqlite.Varint.Defs

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
lean_flags=(-j1 -s 131072 -DautoImplicit=false -E warning --root="$root")
compile() {
  local file=$1
  lake env /usr/bin/time -f '%e s wall, %M KiB peak RSS' lean "${lean_flags[@]}" \
    -o "${file%.lean}.olean" "$file"
}
compile "$src/VersionModel.lean"
compile "$src/VersionCheck.lean"
compile "$src/PutVarintCheck.lean"
lake env lean "${lean_flags[@]}" --run "$src/Replay.lean" \
  "$work/sqlite3.wasm" "$work/canonical.wasm" "$work/version.txt"
(cd "$work" && sha256sum --check "$tool/canonical.sha256")
node "$tool/runtime.mjs" "$(cat "$work/version.txt")" "$work/sqlite3.wasm" "$work/canonical.wasm"
