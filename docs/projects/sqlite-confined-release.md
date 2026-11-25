# One confined lock release under SC and FIFO TSO

[Definitions](../../Silmaril/X86/Concurrency/Sqlite/Release/Defs.lean) ·
[Theorems](../../Silmaril/X86/Concurrency/Sqlite/Release/Thms.lean)

An outlined primitive issues a locked byte RMW that reads `1` and writes
`0` at the selected lock address. An admitted abstract input starts at the
file-control model's release phase with one owner and idle peers. From the
paired implementation input, `confined_sound` proves every weak TSO execution
of that one instruction emits one abstract release and leaves the lock
unowned and the busy count unchanged. Admission requires the initial lock
byte to be `1` and pending writes of all threads to avoid that byte. The
issued footprint is exactly the lock byte. `sc_release_matches` uses the
existing embedding of SC from empty buffers to obtain the same observation.

The per-thread primitive is one instruction. The environment in the proof
may flush any FIFO entry before or after that instruction. It issues no peer
instructions. For a payload byte distinct from the lock, `release_publishes`
proves that the release publishes the owner's initial forwarded view, if no
peer has a pending store to that byte. The owner can have any number of pending
writes to that byte. Its own oldest-first propagation preserves its view
until the locked RMW drains its buffer. The witness forwards a pending value
of 42 while shared memory still shows zero, then commits 42 before release.
The issued-action footprint records the RMW. The confinement premises about
prior pending writes govern propagation separately.

`bottom_sound` holds vacuously. Soundness is downward closed under inclusion
and preserved by union. `top_unsound` exhibits a pair with the right initial
lock byte and release phase where a peer has a matching lock-byte write
pending. The release succeeds as an instruction. A trailing flush then
overwrites the lock byte, so the projected owner contradicts the abstract
post-release owner. The mismatch holds under any choice of allowed footprint.

The example uses the landed [file-control phase model](sqlite-control.md) and
the repository's operational memory model. The separately checked
[`sqlite3_mutex_leave` ELF fragment](sqlite-mutex.md) ends upon entering the
callback. There is no identification of the modeled RMW with a compiled
handler, a pthread implementation, or a SQLite recursion-depth update.
The proof covers a single release boundary and pending propagation under
the stated confinement. Peer instruction issuance, acquisition, fairness,
file-wide SQLite race freedom, and transfer to XL are outside its scope.

```sh
lake build --wfail +Silmaril.X86.Concurrency.Sqlite.Release.Thms
make check CHECK_TARGETS=+Silmaril.X86.Concurrency.Sqlite.Release.Thms
```
