#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 3 ]]; then
  echo 'usage: check.sh WORK_DIR [SQLITE_LEAN_EXE [SQLITE_IMAGE_LEAN_EXE]]' >&2
  exit 2
fi

tool=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$tool/../.." && pwd)
source "$tool/pins.sh"
work=$(cd "$1" && pwd)
shift
lean_bins=()
for exe in "$@"; do
  lean_bins+=("$(realpath "$exe")")
done
check_sha "$shell_sha" "$work/sqlite3.wasm"

tmp=$(mktemp -d "$work/check.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$work/downloads"
fetch "$wasmtime_url" "$wasmtime_sha" "$work/downloads/$wasmtime.tar.xz"
fetch "$wasm_tools_url" "$wasm_tools_sha" "$work/downloads/$wasm_tools.tar.gz"
for archive in "$wasmtime.tar.xz" "$wasm_tools.tar.gz"; do
  tar -xf "$work/downloads/$archive" -C "$tmp"
done

"$tmp/$wasmtime/wasmtime" --version
"$tmp/$wasm_tools/wasm-tools" --version
"$tmp/$wasm_tools/wasm-tools" validate "$work/sqlite3.wasm"
"$tmp/$wasm_tools/wasm-tools" print --skeleton "$work/sqlite3.wasm" |
  sed -n -E '/^  \((import|export) /p' > "$tmp/interface.txt"
diff -u "$tool/interface.txt" "$tmp/interface.txt"
echo 'PASS: core Wasm validation and exact import/export inventory'

native=$repo/corpus/elf/sqlite/x86_64
(cd "$native" && sha256sum --check SHA256SUMS)
ln -s "$native/libsqlite3.so" "$tmp/libsqlite3.so.0"

cd "$repo"
lake build --wfail +Silmaril.Cli.Spec.SqliteShell.Defs +Silmaril.Cli.Io.Run.Defs
lake env lean -DautoImplicit=false -DwarningAsError=true --run "$tool/Check.lean" \
  "$tmp/$wasmtime/wasmtime" "$work/sqlite3.wasm" "$native/sqlite3" "$tmp" "${lean_bins[@]}"
