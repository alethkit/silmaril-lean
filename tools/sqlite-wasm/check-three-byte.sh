#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo "usage: $0 ARCHIVE_DIR WORK_DIR" >&2
  exit 2
fi
tool=$(dirname "$(realpath "$0")")
bash "$tool/check.sh" "$@"

root="$(realpath "$2")/lean"
src="$root/SqliteWasm"
cp "$tool"/{ThreeByteContract,ThreeByteWitness}.lean "$src/"
cd "$tool/../.."
export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
for name in ThreeByteContract ThreeByteWitness; do
  lake env /usr/bin/time -f '%e s wall, %M KiB peak RSS' lean -j1 -s 131072 \
    -DautoImplicit=false -E warning --root="$root" -o "$src/$name.olean" "$src/$name.lean"
done
