#!/usr/bin/env bash
set -euo pipefail
tool=$(cd "$(dirname "$0")" && pwd)
cd "$tool"
sha256sum --check artifact.sha256
cd ../..
lake build --wfail +Silmaril.Formats.Compression.Checksum.Adler32 \
  +Silmaril.Wasm.Binary.Core.Decode +Silmaril.Wasm.Binaryen.Interp
lake env lean -DautoImplicit=false -DwarningAsError=true --run \
  "$tool/InitCheck.lean" "$tool/adler32.wasm"
