# Finite x86-to-SQLite translation relations

[Relation specification](../../Silmaril/X86/Concurrency/Sqlite/Defs.lean)

A proposal is a set of pairs of implementation inputs and SQLite inputs.
For each proposed pair, `Sound` asks that every admitted x86 run project to
a behavior of the SQLite input at the chosen layer. The inclusion is
`projected implementation behaviors ⊆ specification behaviors`. Independently,
every issued memory access must stay within the byte footprint allowed for the
pair. The public judgment validates each execution against the selected
memory semantics and computes its footprint from its actions. A client may
filter admitted executions with a predicate. The observation map only
selects visible events and final state observations.
The [regressions](../../Silmaril/X86/Concurrency/Sqlite/Checks.lean) reject empty
and partial footprints for an erased two-byte store under both SC and TSO.

| Layer | Existing relation | Observation |
| --- | --- | --- |
| Source calls | `SqliteControl.Run CallStep` | Ordered acquire, file-control reply, busy-count restore, release and return events, with final shared owner and busy count |
| Abstract control | `SqliteControl.Run Step` | Same interface, after the call-level cache boundaries have been erased |
| Read-only bytecode | `Vdbe.Trace` | Rows emitted after entry, in order, and the optional halt status |

The layers expose finite prefixes of the named relations. The bytecode relation
covers successful steps of the landed read-only VDBE subset. These signatures
give no guarantees about faults, divergence, scheduling fairness, or which
initial implementation runs exist.

The operational cases use `Tso.SCStep` or `Tso.XWeakStep`.
A client can use the same program trace restriction for either model. Weak TSO steps allow FIFO flushes around an
issued memory event and leave the final buffers available for a boundary check.
The access footprint covers instruction-issued bytes. Initial pending writes,
forwarding, flush confinement and synchronization are separate obligations when
a client interprets an x86 program.

The axiomatic case uses `Litmus.AxReach` and `Lattice.Name.model`. Its
footprint covers the read and write units of the admitted candidate, including
units split for tearing. The models include
SC, strict TSO and the looser XL model of tearing and weak stores. Its trace
vector records thread-indexed program order. A client that observes an order
across threads needs an explicit justification for that order. The operational
FIFO and axiomatic semantics are distinct interpretations.

For fixed observations, footprint and run semantics, the proposal lattice is
the powerset of input pairs. Its meet is intersection, its join is union, its
bottom has no pairs, and its top admits every pair. The soundness follow-up
will check the vacuous bottom case, an inhabited confined case and a rejected
overbroad proposal. The file-control layer already has a
[call-to-control simulation](sqlite-control.md). The concurrent x86 handler
boundary is a separate obligation from the
[pinned mutex dispatch cut](sqlite-mutex.md).

```sh
lake build --wfail +Silmaril.X86.Concurrency.Sqlite.Checks
make check CHECK_TARGETS=+Silmaril.X86.Concurrency.Sqlite.Checks
```
