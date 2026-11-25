# SQLite pthread unlock boundary

The pinned SQLite 3.54.1 x86-64 library travels from `sqlite3_mutex_leave`
to the installed callback. The default pthread callback `pthreadMutexLeave`
is a five-byte tail jump at `0x15560` to the PLT entry at `0xf5c0`. The
entry reads the jump slot at `0x10f2c8`, which has a
`R_X86_64_JUMP_SLOT` relocation for `pthread_mutex_unlock@GLIBC_2.2.5`.
The existing [SQLite wrapper proof](sqlite-mutex.md) supplies the earlier
dispatch boundary. The two jumps and relocation here are disassembly and
ELF inspection evidence.

The repository's separately pinned Ubuntu glibc 2.39 returns dynsym entry
2690 at `0xa1b50` for this versioned reference. Lean checks that the
instruction at `0xa1ba2`, within that entry's 270-byte extent, has bytes
`87 07` and decodes as `xchg dword ptr [rdi], eax`. The existing
`MemEvent.atomic9Accesses` gives one locked RMW across four bytes. In
particular its write footprint includes `rdi + 1`. A singleton footprint
at `rdi` cannot cover this instruction, even when the upper bytes happen to
keep their previous values. [Theorems](../../Silmaril/Elf/Staged/Pinned/GlibcLibc/MutexUnlock/Thms.lean)

The [modeled one-byte release](sqlite-confined-release.md) is therefore too
narrow for an access-preserving identification of this instruction. A
future proof could use a four-byte lock representation, with the mutex's
count and owner fields covered separately. The SQLite source allocates its
connection mutex with `SQLITE_MUTEX_RECURSIVE` in the threaded path. The
glibc wrapper includes a recursive path with a thread-ID check and a
nesting-count decrement. A leave that retains positive depth does not
take the full-release path. The candidate `xchg` path also depends on the
single-thread flag or mutex flags, and the old lock word determines whether
the wake path is taken.

The Lean theorems check per-object lookup, file bytes and the decoded
instruction's access list. Linking the two pins requires an installed
callback and a loader result for the versioned jump slot, then a startup
and instance invariant for the chosen recursive-mutex path. The Ubuntu
pin is an explicit candidate for that obligation. SQLite's Debian build
receipt does not identify it as the library resolved at runtime. The
proof stops at the instruction footprint and provides no loaded
instruction step, pthread return, or SQLite release correspondence.

## Reproduce

```sh
sha256sum corpus/elf/sqlite/x86_64/libsqlite3.so examples/elf/pinned/glibc-libc.so.6
readelf -rW corpus/elf/sqlite/x86_64/libsqlite3.so | rg pthread_mutex_unlock
objdump -d --disassemble=pthreadMutexLeave corpus/elf/sqlite/x86_64/libsqlite3.so
objdump -d --start-address=0xf5c0 --stop-address=0xf5d0 corpus/elf/sqlite/x86_64/libsqlite3.so
readelf -Ws examples/elf/pinned/glibc-libc.so.6 | rg pthread_mutex_unlock
objdump -d --start-address=0xa1b50 --stop-address=0xa1c60 examples/elf/pinned/glibc-libc.so.6
lake build --wfail +Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
make check CHECK_TARGETS=+Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Thms
```

The audited SHA-256 values are
`fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8`
for SQLite and
`3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf`
for glibc.
