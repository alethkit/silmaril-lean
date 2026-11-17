#!/usr/bin/env bash
# The self-contained HTTP server image under Docker: a test, not a proof.
#
#   examples/containers/http-serve/docker-test.sh
#
# Loads ./layout (checking the image ID proved in Silmaril.Containers.HttpServe.Thms and the
# declared port 8080/tcp), starts the container, which listens on 8080 itself, sends one request
# with curl, and checks that the reply is exactly the 40-octet response and that the container
# then exits 0. Port publishing: `-p 127.0.0.1:$PORT:8080` by default; in a sandbox without a
# bridge network, run with DOCKER_NET="--network host" (then the port is 8080).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
elf=b5958d275776a14acd6375e1671db341f6fb37887655397c83683b6a288cc105
config=ed2c4bf8a304749970e5ca9ca9be210d95d63ed9275f68503adf1005f51b178a
layer=249437e992376bda5108c9b513f48b990057aff12ebc4ad2ed65fd5f009230c0
tag=silmaril-http-serve:pinned
port=${PORT:-8080}
net=${DOCKER_NET:--p 127.0.0.1:$port:8080}

tmp=$(mktemp -d)
cid=
cleanup() { [ -n "$cid" ] && docker rm -f "$cid" > /dev/null 2>&1; rm -rf "$tmp"; }
trap cleanup EXIT
printf 'HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok' > "$tmp/expected"

(cd "$here/layout" && sha256sum --quiet -c <(for f in blobs/sha256/*; do echo "${f##*/}  $f"; done))
python3 -I - "$here/layout/blobs/sha256/$layer" "$tmp/from-layer" <<'PY'
import sys, tarfile
with tarfile.open(sys.argv[1]) as t:
    assert t.getnames() == ["http-serve"], t.getnames()
    open(sys.argv[2], "wb").write(t.extractfile("http-serve").read())
PY
echo "$elf  $tmp/from-layer" | sha256sum --quiet -c
if command -v as > /dev/null && command -v ld > /dev/null; then
  sh "$root/examples/verification-projects/theorem-dev/lps-probes/build.sh" "$here/http_serve.s" "$tmp/built" rwx
  echo "$elf  $tmp/built" | sha256sum --quiet -c && echo "1. http_serve.s rebuilds to the pinned ELF in the layer"
else
  echo "1. the layer holds the pinned ELF"
fi

if ! command -v docker > /dev/null || ! docker info > /dev/null 2>&1; then
  echo "skip: docker is not available"
  exit 0
fi
tar -C "$here/layout" -cf "$tmp/image.tar" oci-layout index.json manifest.json blobs
docker load -i "$tmp/image.tar" > /dev/null
[ "$(docker image inspect --format '{{.Id}}' "$tag")" = "sha256:$config" ] || { echo "FAIL: image id"; exit 1; }
[ "$(docker image inspect --format '{{json .Config.ExposedPorts}}' "$tag")" = '{"8080/tcp":{}}' ] ||
  { echo "FAIL: exposed ports"; exit 1; }
echo "2. docker loaded $tag as sha256:$config, exposing 8080/tcp"

# shellcheck disable=SC2086
cid=$(docker run -d $net --read-only --cap-drop ALL --security-opt no-new-privileges "$tag")
echo "3. container $cid started; it listens on 8080 itself"
for _ in $(seq 100); do
  curl -sS --http1.1 -i --max-time 10 "http://127.0.0.1:$port/" > "$tmp/reply" 2> "$tmp/curl.err" && break
  sleep 0.1
done
cmp -s "$tmp/reply" "$tmp/expected" ||
  { echo "FAIL: reply"; od -c "$tmp/reply" | head; cat "$tmp/curl.err"; exit 1; }
echo "4. curl http://127.0.0.1:$port/ received exactly the 40-octet response (200, body ok)"
code=$(timeout 30 docker wait "$cid")
[ "$code" = 0 ] || { echo "FAIL: container exit status $code"; docker logs "$cid"; exit 1; }
echo "5. the container exited 0 after the one session"
echo "PASS (a test of this host, not a proof)"
