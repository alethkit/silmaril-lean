# Linux x86-64 release assets. The SQLite source pins are in corpus/sqlite.
sdk=wasi-sdk-34.0-x86_64-linux
sdk_url=https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-34/$sdk.tar.gz
sdk_sha=b761e3a0721dbae9c09a0059e5fdb2bf917d1b4a8a7b430fb3b5aafb0984b2c4
wasmtime=wasmtime-v50.0.0-x86_64-linux
wasmtime_url=https://github.com/bytecodealliance/wasmtime/releases/download/v50.0.0/$wasmtime.tar.xz
wasmtime_sha=77c19ee0437991f9ac7837b9c269d9c7076744f85dad263fea5214cc2723c7ff
wasm_tools=wasm-tools-1.262.0-x86_64-linux
wasm_tools_url=https://github.com/bytecodealliance/wasm-tools/releases/download/v1.262.0/$wasm_tools.tar.gz
wasm_tools_sha=655b8df67d54c3ef9b52fc237c4e94bbfbb5f5f43825245cb0940a7002a9ed65
shell_sha=b71ec78557631b7a31d27ede9336aa22af9fce926712d2416d9872f18198d2a3

check_sha() {
  printf '%s  %s\n' "$1" "$2" | sha256sum --check
}

# Publish the archive to the cache only after its checksum has passed.
fetch() (
  url=$1 sha=$2 archive=$3
  if [[ -f $archive ]]; then
    check_sha "$sha" "$archive"
  else
    partial=$(mktemp "$archive.XXXXXX")
    trap 'rm -f "$partial"' EXIT
    curl --fail --silent --show-error --location --retry 3 --output "$partial" "$url"
    check_sha "$sha" "$partial"
    mv -f -- "$partial" "$archive"
  fi
)
