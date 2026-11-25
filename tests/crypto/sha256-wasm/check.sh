#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
test_dir=tests/crypto/sha256-wasm
lake=${LAKE:-lake}

"$lake" build --wfail +Silmaril.Wasm.Examples.Sha256Round.Thms
if [[ "${1:-}" == --lean-only ]]; then
  "$lake" env lean -DautoImplicit=false -DwarningAsError=true "$test_dir/Check.lean"
  exit 0
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
clang-19 --target=wasm32-unknown-unknown -O2 -ffreestanding -nostdlib \
  -Wl,--no-entry,--strip-all,--export=sha256_round_a "$test_dir/round.c" -o "$tmp/round.wasm"
printf '%s  %s\n' 4d31b21692befdabad18e921322665a49b056a83e96f18610556c9147225ff87 \
  "$tmp/round.wasm" | sha256sum --check
"$lake" env lean -DautoImplicit=false -DwarningAsError=true --run "$test_dir/Check.lean" "$tmp/round.wasm"
node "$test_dir/kat.mjs" "$tmp/round.wasm"
