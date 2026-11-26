# Checked forwarding through a Sea of Nodes memory diamond

Simple chapter 10 describes pushing a Load through a memory Phi so that
each path can fold against its own Store. This profile handles the case
where both paths can supply the value. The Phi already exports one
scalar alongside the whole-memory value, so the rewrite can route the
first post-join Load's users to that scalar. IR ’95 ties Phi operands to
the arriving Region occurrence and treats the whole Store as a value.
[Pinned Simple chapter 10](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#local-memory-optimizations) ·
[IR ’95 §§2.5 and 3.1](https://doi.org/10.1145/202530.202534)

A candidate names a Store version for each Region slot. Each arm scans
its own table, using the straight-line forwarder's last-Store match at
its exported memory edge. The Store and shared Load must name the same
original address argument. The Store's value origin must be the exact
exported scalar origin, including any reindexing caused by a later Load.
Every later Store changes the version, so an intervening write invalidates
an earlier candidate even when the write uses a different argument.
The address comparison uses wire identity. Different address arguments
may alias.
[Straight-line forwarding](sea-of-nodes-load-forwarding.md) ·
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/Forwarding/Defs.lean)

`checkJoined_latch_reads` proves that the word actually latched at the
arriving occurrence equals a read from that occurrence's selected heap.
`rewrite` removes the initial suffix Load and reindexes every later use.
Every later effect runs in the declared order.
`rewrite_returns_iff` proves preservation and reflection of the returned
word and the entire final heap, for either guard. The scope is total
reads of initialized word cells and this head-Load shape.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/Forwarding/Thms.lean)

The regression checks Stores at different versions that supply the words
`11` and `33`, both Region orders, and a later Store using the removed
Load's result. It rejects swapped candidates, an overwrite, an export of
the old word even with the new Store version, and an arm with no Store.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/Forwarding/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Regression
```
