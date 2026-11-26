#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 3 || ( $1 != --check && $1 != --write ) ]]; then
  echo "Usage: $0 {--check|--write} QUINT_CHECKOUT APALACHE_TGZ" >&2
  exit 2
fi

mode=$1
quint=$(cd "$2" && pwd)
fixtures=$(cd "$(dirname "$0")" && pwd)
quint_sha=95141d4691cce7e60104bdfcbc1d1b074f1cb789
apalache_version=0.62.4
apalache_sha=8ac8488422c30d552735bae11b92a2d014d8e02e8608702acc08f9a2d8a9abb2

if [[ $(git -C "$quint" rev-parse HEAD) != "$quint_sha" ]] ||
   ! git -C "$quint" diff --quiet "$quint_sha" -- quint; then
  echo "Use a clean Quint checkout at $quint_sha" >&2
  exit 1
fi
cli="$quint/quint/dist/src/cli.js"
if [[ ! -f $cli ]]; then
  echo "Run npm ci in $quint/quint to build the pinned CLI" >&2
  exit 1
fi
archive_hash=$(sha256sum < "$3")
if [[ ${archive_hash%% *} != "$apalache_sha" ]]; then
  echo "Apalache archive SHA-256 mismatch, expected $apalache_sha" >&2
  exit 1
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export QUINT_HOME="$work/quint-home"
dist="$QUINT_HOME/apalache-dist-$apalache_version"
mkdir -p "$dist"
tar -xzf "$3" -C "$dist"
cd "$work"

raw_modules=(BoundedCounter BitPair)
modules=("${raw_modules[@]}" ServiceCycle)
for module in "${modules[@]}"; do
  cp "$fixtures/$module.qnt" .
  # A fresh loopback port avoids Quint's default reuse of an already running server.
  port=$(node -e "const server = require('node:net').createServer()
    server.listen(0, '127.0.0.1', () => {
      console.log(server.address().port)
      server.close()
    })")
  node "$cli" compile "$module.qnt" --target=tlaplus --main="$module" --init=init --step=step \
    --apalache-version="$apalache_version" --server-endpoint="127.0.0.1:$port" --verbosity=0 > "$module.tla"
done

tlc() {
  java -Xmx512m -XX:+UseParallelGC -cp "$dist/apalache/lib/apalache.jar" tlc2.TLC -workers 1 "$@"
}

for module in "${raw_modules[@]}"; do
  printf 'INIT q_init\nNEXT q_step\n' > "$module.cfg"
  if ! tlc -deadlock -dump dot "$module.dot" "$module.tla" > "$module.tlc.log" 2>&1; then
    cat "$module.tlc.log" >&2
    exit 1
  fi
done

cp "$fixtures/ServiceReplay.tla" .
printf 'SPECIFICATION Good\nPROPERTY safe weak strong\n' > Good.cfg
printf 'SPECIFICATION Bad\nPROPERTY safe weak\n' > BadWeak.cfg
printf 'SPECIFICATION Bad\nPROPERTY strong\n' > BadStrong.cfg
for run in Good BadWeak; do
  if ! tlc -config "$run.cfg" ServiceReplay.tla > "$run.tlc.log" 2>&1; then
    cat "$run.tlc.log" >&2
    exit 1
  fi
done

status=0
tlc -noGenerateSpecTE -dumpTrace json BadStrong.json -config BadStrong.cfg ServiceReplay.tla \
  > BadStrong.tlc.log 2>&1 || status=$?
if [[ $status != 13 ]] || ! grep -Fxq 'Error: Temporal property strong was violated.' BadStrong.tlc.log; then
  cat BadStrong.tlc.log >&2
  echo "Expected TLC to report a strong-fairness violation (status 13), got status $status" >&2
  exit 1
fi
node "$fixtures/check.cjs" "$quint" "$work"

for module in "${modules[@]}"; do
  if [[ $mode == --check ]]; then
    cmp "$fixtures/$module.tla" "$module.tla"
  else
    cp "$module.tla" "$fixtures/"
  fi
done
cd "$fixtures"
if [[ $mode == --check ]]; then
  sha256sum -c SHA256SUMS
else
  sha256sum BitPair.qnt BitPair.tla BoundedCounter.qnt BoundedCounter.tla oracle.json \
    ServiceCycle.qnt ServiceCycle.tla ServiceReplay.tla > SHA256SUMS
fi
