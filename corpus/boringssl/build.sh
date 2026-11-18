#!/usr/bin/env bash
# Repository-authored embedding build of pinned upstream C/C++/assembly inputs.
. "$(dirname "$0")/../common.sh"
start_build boringssl "$1" "$2"
ROOT=boringssl-ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6
A=$(archive "$ROOT.tar.gz" 75ee588268ae3d7552f5be7e0849bdcc8e4159f22547dbfb4aae997784fdd345 https://codeload.github.com/google/boringssl/tar.gz/ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6)
extract "$A" "$BUILD"; pristine "$A"
cd "$BUILD/$ROOT"
CONFIG=${CORPUS_BORINGSSL_CONFIG:-no-asm}
python3 -I "$CORPUS/boringssl/embed.py" "$PWD" "$TP" "$BASE_CFLAGS" "$CONFIG"
info cflags "$BASE_CFLAGS -fPIC -pthread -DBORINGSSL_IMPLEMENTATION -DBORINGSSL_SHARED_LIBRARY -Iinclude -MMD -MP; C++17 -fno-exceptions -fno-rtti; config=$CONFIG (see embedding-plan.json)"
info ldflags 'shared libraries: g++ -shared -pthread; upstream bssl: g++ -pthread; see exact embedding plan/log'
info configure_args "upstream source-list embedding; $CONFIG; NON-FIPS"
info command "python3 -I /corpus/boringssl/embed.py $PWD $TP '$BASE_CFLAGS' $CONFIG"
info command "make -f embed.mk -j$JOBS --output-sync=target all"
make -f embed.mk -j"$JOBS" --output-sync=target all > embed-build.log 2>&1 || { tail -60 embed-build.log; exit 1; }
cp libcrypto.so libssl.so bssl "$OUTDIR/"
mkdir "$OUTDIR/supplementary"
cp boringcrypto-bcm.o "$OUTDIR/supplementary/"
"${TP}readelf" -hSWsr boringcrypto-bcm.o > "$OUTDIR/supplementary/boringcrypto-bcm.readelf.txt"
"${TP}nm" -u boringcrypto-bcm.o > "$OUTDIR/supplementary/boringcrypto-bcm.undefined.txt"
cp embedding-plan.json "$OUTDIR/supplementary/"
{ depfiles "$PWD"; find "$PWD/crypto" "$PWD/util/pregenerate" -type f \( -name '*.pl' -o -name '*.go' \)
  printf '%s\n' "$PWD/LICENSE" "$PWD/gen/sources.json" "$PWD/gen/README.md" "$PWD/CMakeLists.txt" "$PWD/crypto/fipsmodule/FIPS.md" "$PWD/embedding-plan.json" "$PWD/embed.mk" "$PWD/embed-build.log" "$PWD/go.mod" "$PWD/go.sum" "$PWD/util/build/build.go"; } | collect "$PWD" "$ROOT"
