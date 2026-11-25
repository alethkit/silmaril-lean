# Finite x86-to-SQLite translation relations

[Relation specification](../../Silmaril/X86/Concurrency/Sqlite/Defs.lean)

A proposal is a set of pairs of implementation inputs and SQLite inputs.
For each proposed pair, `Sound` asks that every admitted x86 run project to
a behavior of the SQLite input at the chosen layer. The inclusion is
`projected implementation behaviors ⊆ specification behaviors`. Independently,
every issued memory access must stay within the byte footprint allowed for the
pair. Erasing an event from the trace does not exempt its access from that check.

| Layer | Existing relation | Observation |
| --- | --- | --- |
| Source calls | `SqliteControl.Run CallStep` | Ordered acquire, file-control reply, busy-count restore, release and return events, with final shared owner and busy count |
| Abstract control | `SqliteControl.Run Step` | Same interface, after the call-level cache boundaries have been erased |
| Read-only bytecode | `Vdbe.Trace` | Rows emitted after entry, in order, and the optional halt status |

The layers expose finite prefixes of the named relations. The bytecode relation
covers successful steps of the landed read-only VDBE subset. These signatures
give no guarantees about faults, divergence, scheduling fairness, or which
initial implementation runs exist.

The operational adapters use the same program trace restriction with
`Tso.SCStep` or `Tso.XWeakStep`. Weak TSO steps allow FIFO flushes around an
issued memory event and leave the final buffers available for a boundary check.
The access footprint covers instruction-issued bytes. Initial pending writes,
forwarding, flush confinement and synchronization are separate obligations when
a client interprets an x86 program.

The axiomatic adapter uses `Litmus.AxReach` and `Lattice.Name.model`, including
SC, strict TSO and the looser XL model of tearing and weak stores. Its trace
vector records thread-indexed program order. A client that observes an order
across threads needs an explicit justification for that order. The operational
FIFO adapter and the axiomatic adapter are distinct interpretations.

For fixed observations, footprint and run semantics, the proposal lattice is
the powerset of input pairs. Its meet is intersection, its join is union, its
bottom has no pairs, and its top admits every pair. The soundness follow-up
will check the vacuous bottom case, an inhabited confined case and a rejected
overbroad proposal. The file-control layer already has a
[call-to-control simulation](sqlite-control.md). The concurrent x86 handler
boundary is a separate obligation from the
[pinned mutex dispatch cut](sqlite-mutex.md).

```sh
lake build --wfail +Silmaril.X86.Concurrency.Sqlite.Defs
make check CHECK_TARGETS=+Silmaril.X86.Concurrency.Sqlite.Defs
```
