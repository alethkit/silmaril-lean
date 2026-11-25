# SQLite 3.54.1 with GCC and Clang

`manifest.json` pins the same official SQLite amalgamation, default
configuration (`SQLITE_THREADSAFE=1`), optimization level, compile and link
arguments, and build environment for both outputs. The source span is the actual
`sqlite3_libversion_number(void)` definition, which returns
`SQLITE_VERSION_NUMBER`. The GCC output matches the repository's existing
unstripped O2 artifact byte for byte. Rebuild the Clang ELF from the pinned
inputs.

| Compiler | ELF size | `.dynsym` index | Symbol VA range | File byte range | `DT_NEEDED` |
| --- | ---: | ---: | --- | --- | --- |
| Debian GCC 14.2.0-19 | 1,208,160 | 311 | `[0x13820, 0x13826)` | `[0x13820, 0x13826)` | `libc.so.6` |
| Debian Clang 19.1.7-3+b1 | 1,321,024 | 312 | `[0x249a0, 0x249a6)` | `[0x249a0, 0x249a6)` | `libm.so.6`, `libc.so.6` |

Both compiler drivers use GNU ld 2.44 and target the System V AMD64 ABI.
Both outputs are little-endian ELF64 shared objects with soname
`libsqlite3.so.0`. The drivers use different implicit linker arguments. The
Clang link retains the explicitly requested `-lm` dependency, while the GCC
link uses `--as-needed` before it and drops it. The rebuild log includes each
driver's resolved link command. Both selected global `STT_FUNC` symbols lie
within file-backed executable `PT_LOAD` ranges and contain
`b8 b1 99 2e 00 c3` (`mov $3054001,%eax; ret`). Neither instruction depends
on an address specific to its ELF.

## Lean witness

`libversionNumber_firstReturn` takes an arbitrary `Open.isa` state with the
six bytes loaded at the entry RIP and a System V `AbiEntry` (stack
alignment and a readable return word). It proves a two-step first return
with RAX equal to 3054001, a System V `AbiReturn` (return RIP, popped stack,
and preserved callee-saved registers), and equality of final and initial
memory. `libversionNumber_pair` applies this to two independent entries
and proves equal first-return RAX with each side preserving its own
memory. It allows different entry addresses and different caller states.

The file checker binds the six modeled bytes to the two pinned ELF slices
using hashes, dynamic symbols, and executable segment extraction. The
existing GCC file witnesses are linked in the manifest. Clang's complete
ELF is checked by the replay script and ELF readers. Lean checks the
extracted bytes' equality to its proof input and the machine run from the
loaded-byte premise. The result covers this one same-code function. It
does not model dynamic loading or interposition, prove reference C
semantics, or relate the libraries' other functions or dependencies.

The manifest reuses the existing binary-equivalence endpoint and function
fields. It has a distinct schema because the compiler viewer's existing
manifest contract requires both artifacts to be committed and each pair
to be an unproved obligation. This manifest records one reconstructed
artifact and a checked loaded-slice theorem. The viewer and canonical
registry entries for the historical pairs remain as they are.

## Replay

From the repository root, with Docker BuildKit, GNU binutils, Python 3,
`curl`, and `unzip` available:

```sh
set -eu
pair_dir="$PWD/corpus/sqlite/equivalence/native-compilers"
scratch=$(mktemp -d)
mkdir "$scratch/src" "$scratch/out"
archive="$scratch/sqlite-amalgamation-3540100.zip"
curl -fsSL --max-time 60 https://sqlite.org/2026/sqlite-amalgamation-3540100.zip -o "$archive"
printf '%s  %s\n' 0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9 "$archive" | sha256sum -c -
unzip -p "$archive" sqlite-amalgamation-3540100/sqlite3.c > "$scratch/src/sqlite3.c"
unzip -p "$archive" sqlite-amalgamation-3540100/sqlite3.h > "$scratch/src/sqlite3.h"

timeout 180 docker build --network host --platform linux/amd64 \
  --secret id=bootstrap_ca,src=/etc/ssl/certs/ca-certificates.crt \
  -t silmaril-sqlite-native:c3 "$pair_dir"
timeout 180 docker run --rm --network host --platform linux/amd64 \
  --mount "type=bind,src=$scratch/src,dst=/src,readonly" \
  --mount "type=bind,src=$pair_dir/build-in-container.sh,dst=/build-pair.sh,readonly" \
  --mount "type=bind,src=$scratch/out,dst=/out" \
  silmaril-sqlite-native:c3 bash /build-pair.sh

python3 -B "$pair_dir/verify.py" --archive "$archive" \
  --gcc "$scratch/out/libsqlite3-gcc.so" --clang "$scratch/out/libsqlite3-clang-19.so" \
  --lean-check "$scratch/CheckSlices.lean"
lake build --wfail Silmaril.Elf.Corpus.SqliteNativeCompilers.Thms
lake env lean -DwarningAsError=true "$scratch/CheckSlices.lean"
```

Pass a different host CA bundle path to BuildKit if required. Debian's
signed snapshot authenticates the package index regardless of the path
used to bootstrap TLS. The last command also prints the transitive axiom
footprints of the exported byte list and both theorems.
