#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo 'usage: build.sh ARCHIVE_DIR OUTPUT.wasm' >&2
  exit 2
fi

tool=$(cd "$(dirname "$0")" && pwd)
archives=$(cd "$1" && pwd)
output=$(realpath -m "$2")
temp=$(mktemp -d)
trap 'rm -rf "$temp"' EXIT

cd "$archives"
sha256sum --check <<'HASHES'
9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23  zlib-1.3.1.tar.gz
b761e3a0721dbae9c09a0059e5fdb2bf917d1b4a8a7b430fb3b5aafb0984b2c4  wasi-sdk-34.0-x86_64-linux.tar.gz
HASHES
tar -xzf zlib-1.3.1.tar.gz -C "$temp"
tar -xzf wasi-sdk-34.0-x86_64-linux.tar.gz -C "$temp"

cd "$temp/zlib-1.3.1"
sha256sum --check <<'HASHES'
9cd1443a24ff2a3053961695bd432035c58347386a420d3388232376ebabe211  adler32.c
8a5579af72ea4f427ff00a4150f0ccb3fc5c1e4379f726e101133b1ab9fc600c  zlib.h
f5134250a67d57459234b63858f0d9d3ef8dcc48e9e1028d3f4fdcf6eae677ae  zconf.h
dddb2dc7a1dc339ecf2c8e089b366f08bb731c0839c7110240d17ce731bb4fea  zutil.h
HASHES
"$temp/wasi-sdk-34.0-x86_64-linux/bin/clang" --target=wasm32-wasip1 -O2 -nostdlib \
  -Wl,--no-entry -Wl,--strip-all -Wl,--export=adler32 -Wl,--export=adler32_z \
  -Wl,--export-memory -o "$temp/adler32.wasm" adler32.c

cd "$temp"
sha256sum --check "$tool/artifact.sha256"
install -m 0644 adler32.wasm "$output"
