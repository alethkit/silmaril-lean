#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo "usage: $0 INPUT.wasm QUOTED_NAMESPACE_DIR" >&2
  exit 2
fi
wasm=$(realpath "$1")
src=$(realpath "$2")
root=$(dirname "$src")
namespace=$(basename "$src")
tool=$(dirname "$(realpath "$0")")
case "$namespace" in
  SqliteWasm)
    fixture="$tool"
    manifest="$fixture/reactor.json"
    ;;
  SqliteWebWasm)
    fixture="$tool/../sqlite-web-wasm"
    manifest="$fixture/release.json"
    ;;
  *) echo "unsupported proof fixture: $namespace" >&2; exit 2 ;;
esac
cd "$tool/../.."

# Check the original bytes independently of the generated metadata and code fragments.
python3 - "$manifest" "$wasm" "$src/Original.wasm" <<'PY'
import hashlib
import json
import sys
from pathlib import Path

expected = json.loads(Path(sys.argv[1]).read_text())["artifact_sha256"]
original = Path(sys.argv[2]).read_bytes()
if hashlib.sha256(original).hexdigest() != expected:
    sys.exit("Wasm SHA-256 does not match the proof fixture manifest")
Path(sys.argv[3]).write_bytes(original)
PY
cp "$tool/ArtifactEntries.lean" "$root/SqliteWasmArtifactEntries.lean"
cp "$fixture/ArtifactCheck.lean" "$src/ArtifactCheck.lean"
cat > "$src/Original.lean" <<LEAN
module

public import Silmaril.Prelude.Bytes.Elab.Defs
public import Silmaril.Wasm.Binary.Packed.Defs

namespace $namespace

kbytes_def originalBytes from_file "Original.wasm"

@[expose] public noncomputable def original : Silmaril.Wasm.Binary.Packed.Cursor :=
  ⟨originalBytes, originalBytes.wf_true, 0⟩

end $namespace
LEAN

lake build --wfail +Silmaril.Wasm.Binary.Packed.Defs +Silmaril.Wasm.Component.Chunked.Defs
export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
for file in "$root/SqliteWasmArtifactEntries.lean" "$src/Original.lean" "$src/ArtifactCheck.lean"; do
  lake env /usr/bin/time -f '%e s wall, %M KiB peak RSS' lean -j1 -s 131072 \
    -DautoImplicit=false -E warning --root="$root" -o "${file%.lean}.olean" "$file"
done
