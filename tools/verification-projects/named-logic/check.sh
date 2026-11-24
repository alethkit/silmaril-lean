#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
revision=$(git rev-parse --verify "${1:?provide the commit of the checked database examples}^{commit}")
out=${2:?provide an output directory}
tool=tools/verification-projects/named-logic
shift 2
if (( $# > 1 )) || [[ ${1:-} != "" && $1 != --interpretations ]]; then
  echo "usage: $0 revision output-dir [--interpretations]" >&2
  exit 2
fi
if [[ ${1:-} == --interpretations ]]; then
  git diff --exit-code "$revision" -- lean-toolchain lake-manifest.json \
    Silmaril/Logic/HOLLight Silmaril/Proofs/Logic/HOLLight
  git cat-file -e "$revision:Silmaril/ProofFormats/DaslSyntax/Database/Examples/Model/Thms.lean"
fi
git diff --exit-code "$revision" -- Silmaril/ProofFormats/DaslSyntax Silmaril/Proofs/ProofFormats/DaslSyntax
mkdir -p "$out"
lake build --wfail +Silmaril.ProofFormats.DaslSyntax.Database.Examples.Model.Thms
lake env lean -DwarningAsError=true --run "$tool/Export.lean" "$revision" "$@" > "$out/named-logic-plan.json"
python3 -BEs "$tool/manifest.py" build "$out/named-logic-plan.json" "$out/named-logic.json"
python3 -BEs "$tool/manifest.py" verify "$out/named-logic-plan.json" "$out/named-logic.json"
python3 -BEs "$tool/test_manifest.py" "$out/named-logic-plan.json"
if [[ ${1:-} == --interpretations ]]; then
  lake env lean -DwarningAsError=true tests/formats/DaslDatabaseModel.lean > "$out/named-logic-axioms.txt"
fi
sha256sum "$out/named-logic-plan.json" "$out/named-logic.json" > "$out/named-logic-sha256.txt"
