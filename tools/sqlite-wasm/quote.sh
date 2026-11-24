#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 3 ]]; then
  echo "usage: $0 MANIFEST.json INPUT.wasm OUTPUT_DIR" >&2
  exit 2
fi
manifest=$(realpath "$1")
input=$(realpath "$2")
src=$(realpath -m "$3")
root=$(dirname "$src")
tool=$(dirname "$(realpath "$0")")
cd "$tool/../.."

python3 "$tool/generate.py" --manifest "$manifest" "$input" "$src"
helper="$root/SqliteWasmQuote.lean"
cp "$tool/Quote.lean" "$helper"
lake build --wfail +Silmaril.Wasm.Binary.Quote.Defs

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
compile() {
  local file=$1
  lake env /usr/bin/time -f '%e s wall, %M KiB peak RSS' lean -j1 -s 131072 \
    -DautoImplicit=false -E warning --root="$root" -o "${file%.lean}.olean" "$file"
}
compile "$helper"
while IFS= read -r module; do
  compile "$src/$module.lean"
done < "$src/modules.txt"
