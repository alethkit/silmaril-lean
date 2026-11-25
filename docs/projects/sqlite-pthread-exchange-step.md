# The glibc exchange step and FIFO TSO publication

The [pinned exchange](sqlite-pthread-unlock.md) is a four-byte locked RMW.
[`step_and_publication`](../../Silmaril/Elf/Staged/Pinned/GlibcLibc/MutexUnlock/Step/Thms.lean)
relates one loaded Atomic9 exchange to the central transition of a FIFO TSO
weak step. Its hypotheses supply the actual fetch result, aligned RDI, zero
RAX, read and write permission on the dword, and equality of the machine byte
view with the shared TSO memory at issue. They also supply the leading and
trailing FIFO flushes, an empty issuer buffer at issue, and old lock bytes
`[1, 0, 0, 0]`.

The Atomic9 step advances RIP by two, returns the old dword in RAX, clears
the lock dword, and preserves the mappings and all bytes outside it. The
result's entire byte view equals the central TSO memory update. Trailing
propagation cannot restore the lock because no initial pending write
overlaps its four bytes. For each outside byte that no peer has pending,
the final TSO shared memory equals the owner's initial forwarded view.
Progress to the exchange and the exact leading and trailing flushes are
hypotheses of this proof.

The checked ELF lookup and bytes identify a candidate instruction. A
loader result still has to relate SQLite's installed callback and versioned
jump slot to a concrete glibc instance. A separate path proof must establish
ownership, the TLS/recursive-depth and mutex-kind guards, and the old-lock
value at the exchange. It must account for the owner/count/stack operations
outside the exchange and show which wake or return path follows. Here the
read and write permissions and interference hypotheses apply to the exchange
cut. No SQLite handler return, general peer instruction interleaving, or XL
execution theorem follows from this cut alone.

```sh
lake build --wfail +Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Step.Thms
make check CHECK_TARGETS=+Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Step.Thms
```
