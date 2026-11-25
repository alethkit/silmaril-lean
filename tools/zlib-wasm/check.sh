#!/usr/bin/env bash
set -euo pipefail
tool=$(cd "$(dirname "$0")" && pwd)
cd "$tool"
sha256sum --check artifact.sha256
cd ../..
lake build --wfail +Silmaril.Wasm.Binary.Core.Decode +Silmaril.Wasm.ModuleParts.Defs \
  +Silmaril.Wasm.Validation.Check.Validate
lake env lean -DautoImplicit=false -DwarningAsError=true --run \
  "$tool/Decode.lean" "$tool/adler32.wasm"
node "$tool/runtime.mjs" "$tool/adler32.wasm"
