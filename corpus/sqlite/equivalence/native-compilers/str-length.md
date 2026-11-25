# SQLite length query across GCC and Clang

The same pinned SQLite 3.54.1 artifacts used for the version query contain
distinct `sqlite3_str_length` bodies. The source function returns
`p ? p->nChar : 0`. The manifest pins both the function definition and the
`struct sqlite3_str` declaration in the amalgamation.

| Compiler | Dynamic symbol | VA range | File byte range | Exact slice |
| --- | ---: | --- | --- | --- |
| GCC | 288 | `[0x10060, 0x1006b)` | `[0x10060, 0x1006b)` | `31 c0 48 85 ff 74 03 8b 47 18 c3` |
| Clang | 289 | `[0x12e70, 0x12e7c)` | `[0x12e70, 0x12e7c)` | `48 85 ff 74 04 8b 47 18 c3 31 c0 c3` |

The following offsets are relative to each function's own entry address.

| Compiler | Common prefix | Null path from branch | Non-null path from branch |
| --- | --- | --- | --- |
| GCC | `0 xor %eax,%eax → 2 test %rdi,%rdi → 5 je` | `10 ret` | `7 mov 24(%rdi),%eax → 10 ret` |
| Clang | `0 test %rdi,%rdi → 3 je` | `9 xor %eax,%eax → 11 ret` | `5 mov 24(%rdi),%eax → 8 ret` |

`StrLength.strLength_pair` uses the two exact loaded slices and System V
entry states. The entries must agree on whether RDI is zero. For each non-null
entry, a read of four bytes starting at its own RDI + 24 must give the same
32-bit value. Lean proves that both runs first-return with RAX equal to zero
for null or the zero-extended 32-bit value for non-null, and each final
memory equals its respective entry memory. The field is read only on the
non-null path. The ABI return slot is read on both paths.

The file check and the machine theorem have separate premises. File checks
cover whole-file digests, executable ranges, dynamic symbols, and the source
spans. Lean checks the two extracted byte lists against its proof inputs and
the state transitions. The guarantee starts after the bytes have been loaded
and uses modeled readable memory. It covers neither C pointer validity nor a
correspondence between C and machine execution.

## Replay

Use the build recipe in [README.md](README.md), then run the symbol-specific
check from the same shell.

```sh
python3 -B "$pair_dir/verify.py" --symbol sqlite3_str_length --archive "$archive" \
  --gcc "$scratch/out/libsqlite3-gcc.so" --clang "$scratch/out/libsqlite3-clang-19.so" \
  --lean-check "$scratch/CheckStrLength.lean"
lake build --wfail Silmaril.Elf.Corpus.SqliteNativeCompilers.StrLength.Thms
lake env lean -DwarningAsError=true "$scratch/CheckStrLength.lean"
```

The layout observation also replays with both pinned compilers. In the source
directory extracted for the build, compile a file containing the following
three lines with the recorded compile flags, substituting `-fsyntax-only`
for the output and compile-only arguments.

```c
#include "sqlite3.c"
_Static_assert(__builtin_offsetof(struct sqlite3_str, nChar) == 24, "nChar offset");
_Static_assert(sizeof(((struct sqlite3_str *)0)->nChar) == 4, "nChar width");
```
