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

if [[ $(basename "$src") != SqliteWasm || ! -f "$src/Original.olean" || ! -f "$src/MetadataVectors.olean" ]]; then
  echo 'run the reactor quotation, artifact check and metadata-vectors check first' >&2
  exit 2
fi

python3 - "$src" "$tool/../reactor.json" <<'PY'
import hashlib
import json
import sys
from pathlib import Path

root = Path(sys.argv[1])
wasm = (root / "Original.wasm").read_bytes()
pin = json.loads(Path(sys.argv[2]).read_text())["artifact_sha256"]
if hashlib.sha256(wasm).hexdigest() != pin:
    sys.exit("Original.wasm does not match the reactor pin")
for segment, start, end in ((0, 683415, 734785), (1, 734793, 741717)):
    (root / f"DataPayload{segment}.bin").write_bytes(wasm[start:end])
PY

cp "$tool"/{DataSectionEvidence,DataSection}.lean "$src/"
cp "$tool/ImportCheck.lean" "$src/DataSectionImportCheck.lean"

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
for name in DataSectionEvidence DataSection DataSectionImportCheck; do
  file="$src/$name.lean"
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" lean -j1 -s 131072 -M 6144 \
    -DautoImplicit=false -DwarningAsError=true --root="$root" -o "${file%.lean}.olean" "$file"
done
