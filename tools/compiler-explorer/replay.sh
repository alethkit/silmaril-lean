#!/usr/bin/env bash
# Replay the kernel on the compiler explorer's evidence modules with the toolchain's `leanchecker`
# (`make compiler-explorer-check` runs it). Each named module's own declarations are re-added to an
# environment, through the kernel, on top of its imports as loaded from their .olean files; the
# imports are not replayed (`--fresh`, the whole closure with Mathlib, is not run). It is the same
# kernel as `lake build`, run again on the stored declarations, not an independent implementation.
set -euo pipefail
cd "$(dirname "$0")/../.."
LAKE="${LAKE:-lake}"
checker="$(dirname "$("$LAKE" env which lean)")/leanchecker"
modules=(
  Silmaril.Proofs.Compiler.CompilesTo.Sim.Compose
  Silmaril.Proofs.Compiler.Explorer.Basic
  Silmaril.Proofs.Compiler.Explorer.Det
  Silmaril.Compiler.Explorer.Decompiled.Thms
  Silmaril.Proofs.Project.Shapes.CompilesTo.Explorer
  CompilesToExamples.Explorer.Builds
  CompilesToExamples.Explorer.Code
  CompilesToExamples.Explorer.Decompiled
  CompilesToExamples.Explorer.Rows
)
# The pinned leanchecker accepts multiple targets and replays each from its own
# imports (LeanChecker.checkOlean). Share one startup and a bounded task pool.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
if ! [[ "$LEAN_NUM_THREADS" =~ ^[1-9][0-9]*$ ]]; then
  echo "LEAN_NUM_THREADS must be a positive integer" >&2
  exit 1
fi
start=$(date +%s)
timeout 1200 "$LAKE" env "$checker" --verbose "${modules[@]}"
for m in "${modules[@]}"; do
  echo "leanchecker $m: ok (batched)"
done
echo "leanchecker batch: ${#modules[@]} targets ($(( $(date +%s) - start )) s)"
