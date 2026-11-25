#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 ]]; then
  echo "usage: $0 INPUT.wasm" >&2
  exit 2
fi
wasm=$(realpath "$1")
tool=$(dirname "$(realpath "$0")")
cd "$tool/../../.."

python3 - "$tool/../reactor.json" "$wasm" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

pin = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))["artifact_sha256"]
if hashlib.sha256(Path(sys.argv[2]).read_bytes()).hexdigest() != pin:
    sys.exit("Wasm SHA-256 does not match the reactor pin")
PY

/usr/bin/time -f 'validator prerequisites: %e s wall, %M KiB peak RSS' \
  timeout 300 lake build --wfail +Silmaril.Wasm.Validation.Check.Validate
for mode in parse validate; do
  for repetition in 1 2 3; do
    printf '%s run %s\n' "$mode" "$repetition"
    lake env /usr/bin/time -f '%e s wall, %M KiB peak RSS' \
      timeout 60 lean -j1 -s 131072 -M 6144 -DautoImplicit=false -DwarningAsError=true \
      --run "$tool/Benchmark.lean" "$mode" "$wasm"
  done
done
