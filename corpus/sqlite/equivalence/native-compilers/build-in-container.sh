#!/usr/bin/env bash
set -euo pipefail

export SOURCE_DATE_EPOCH=1762128000 LC_ALL=C TZ=UTC
mkdir -p /build/sqlite
cd /build/sqlite
cp /src/sqlite3.c /src/sqlite3.h .
sha256sum -c <<'HASHES'
0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52  sqlite3.c
d6c84557261893439b341d2e6c35187ae3ea24fbfd843ad94616f72d89242b8c  sqlite3.h
HASHES

dpkg-query -W gcc gcc-14 clang-19 libc6-dev binutils
ld --version | sed -n '1p'
cflags=(-O2 -g0 -ffile-prefix-map=/build/sqlite=. -DSQLITE_THREADSAFE=1 -MMD -fPIC)
ldflags=(-shared -Wl,-soname,libsqlite3.so.0 -o libsqlite3.so sqlite3.o -lm)
for compiler in gcc clang-19; do
    "$compiler" --version
    time "$compiler" "${cflags[@]}" -c sqlite3.c -o sqlite3.o
    "$compiler" -### "${ldflags[@]}" 2>&1
    "$compiler" "${ldflags[@]}"
    cp libsqlite3.so "/out/libsqlite3-$compiler.so"
    rm sqlite3.o sqlite3.d libsqlite3.so
done
sha256sum /out/libsqlite3-gcc.so /out/libsqlite3-clang-19.so
