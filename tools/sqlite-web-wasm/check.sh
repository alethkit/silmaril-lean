#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo "usage: $0 SQLITE_WEB_ZIP WORK_DIR" >&2
  exit 2
fi
archive=$(realpath "$1")
mkdir -p "$2"
work=$(realpath "$2")
tool=$(dirname "$(realpath "$0")")
cd "$tool/../.."

printf '%s  %s\n' 85ebce90b6d189442b29e11d193337b5e63203aae9b6590dbe89a601b9891da2 "$archive" |
  sha256sum --check
mkdir -p "$work/release/jswasm"
for filename in sqlite3.wasm sqlite3.mjs; do
  unzip -p "$archive" "sqlite-wasm-3540100/jswasm/$filename" > "$work/release/jswasm/$filename"
done

root="$work/lean"
wasm="$work/release/jswasm/sqlite3.wasm"
bash tools/sqlite-wasm/quote.sh "$tool/release.json" "$wasm" "$root/SqliteWebWasm"
lake build --wfail +Silmaril.Wasm.Binaryen.Exe.Decode
cp "$tool/Replay.lean" "$root/WebReplay.lean"
export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
lake env lean -j1 -s 131072 -DautoImplicit=false -E warning --root="$root" \
  --run "$root/WebReplay.lean" "$wasm" "$work/canonical.wasm"
sha256sum "$wasm" "$work/release/jswasm/sqlite3.mjs" "$work/canonical.wasm"
