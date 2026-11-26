# Delete a checked overwritten Store

In Simple chapter 10, `StoreNode.idealize` bypasses an earlier Store to
the same pointer and field when the earlier memory node has no other
uses. The chapter also shows a Load that must observe a value before a
later Store, and why effect sharing across control paths can create an
extra write. This formalization uses the admitted straight-line native
`Memory.Graph` table and its coherent, latest-version memory edges.
[Pinned StoreNode implementation](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L74) ·
[Pinned chapter 10 examples](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#local-memory-optimizations) ·
[IR ’95 §2.5](https://doi.org/10.1145/202530.202534)

Nominate two one-based Store versions in the original table. The checker
requires both Stores to use the same original typed address port and
finds the overwrite strictly after the Store to delete. Every intervening
Load needs a covered reader port and a concrete cell inequality from the
existing `Disjoint.Certificate`. A same-wire Load fails the static check.
The invocation checker rejects coinciding cells on different ports.
Intervening Stores remain in order with all their operands.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Defs.lean) ·
[Address certificate](../../Silmaril/SSA/SeaOfNodes/Memory/Forwarding/Disjoint/Thms.lean)

The rewrite removes the first nominated Store from the native graph and
reconnects its suffix with the new live memory versions. Its scalar
ports stay in scope because a Store produces only memory. The proof
tracks equal heaps outside the observed cell and equal scalar locals
through the gap. The checked overwrite restores equality of the entire
heap. The explicit-edge correspondence then gives preservation and
reflection of the returned word and whole final heap.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Thms.lean)

The fixture restores the initial value after logging a disjoint read.
If the reader aliases the removed Store's cell, deleting that Store
would change both Return and the logging cell. The checker rejects that
input. It also rejects missing reader coverage and an overwrite to a
different port. The scope is the ordered, initialized word-cell profile
with one supplied pair of Store versions.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/DeadStore/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Regression
```
