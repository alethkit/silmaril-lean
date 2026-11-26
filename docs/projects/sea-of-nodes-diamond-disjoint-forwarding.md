# Post-join forwarding across certified disjoint Stores

The first Load after the Region supplies the original address argument
to observe. Each incoming slot has a certificate naming one nominated
Store and the address arguments of its later Stores. The checker validates
each certificate against the concrete typed cells, then scans only that
slot's arm. A retained Store word must be the exact scalar exported with
the arm's final memory. Port identity associates a write with its
certificate entry. The check of `Fin cells` inputs supplies the
disequality used to prove that the write preserves the observed cell.
[Joined forwarding](sea-of-nodes-memory-diamond-forwarding.md) ·
[Straight-line disjoint forwarding](sea-of-nodes-disjoint-load-forwarding.md) ·
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/Forwarding/Disjoint/Defs.lean)

The arm exit check reuses the straight-line forwarder's stored-word
invariant and uses the current heap after all arm writes. Both Region
slots must pass. The actual arrival supplies the word and memory to the
suffix. The joined rewriter removes the first Load and redirects its
users to the latched word. `rewrite_returns_iff` proves preservation and
reflection on the returned word and entire final heap for either guard,
at the checked input and any initial heap.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/Forwarding/Disjoint/Thms.lean)

The regression gives the two branches different Store versions,
forwarded words, and disjoint writer arguments. It tests both slot orders
and either guard. It also makes the false arm's writer alias the observed
cell while the true arm's check still succeeds, and tests rejection when
the false arm lacks the writer fact. The scope is the initial suffix Load
of a memory diamond over initialized word cells.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/Forwarding/Disjoint/Regression.lean)

The source correspondence combines IR ’95's incoming Region occurrences
and whole-memory value with Simple chapter 10's folding of a Load on each
incoming memory path.
[IR ’95 §§2.5 and 3.1](https://doi.org/10.1145/202530.202534) ·
[Pinned Simple chapter 10](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#local-memory-optimizations)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Correctness
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Correctness
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint.Regression
```
