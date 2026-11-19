#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
tool=tools/artifact-naming
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

python3 -I "$tool/test_verify.py"
python3 -I "$tool/verify.py" verify "$tool/fixtures.tsv" --emit-lean > "$work/ArtifactNamingRows.lean"
(cd "$work" && lean -DwarningAsError=true -o ArtifactNamingRows.olean ArtifactNamingRows.lean)
export LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}"
lake env lean -DwarningAsError=true --run tests/formats/ArtifactNaming.lean "$work/title.cbor"
expected=$(awk -F '\t' '$1 == "title" {print $5}' "$tool/fixtures.tsv")
actual=$(python3 -I "$tool/verify.py" name dasl drisl sha256 "$work/title.cbor")
test "$actual" = "$expected"
printf 'Lean-emitted title, externally named: %s\n' "$actual"
