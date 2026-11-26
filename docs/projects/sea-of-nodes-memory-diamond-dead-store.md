# Delete a Store overwritten on both diamond occurrences

Simple chapter 10 joins the incoming memory from a conditional Store
using a memory Φ. Its local Store-after-Store rewrite checks the same
pointer and field and the old Store's memory users. The chapter also
shows how a read before an overwrite can observe the earlier write.
[Pinned Simple memory Φ](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable) ·
[Pinned StoreNode rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[IR ’95 §§2.5 and 3.1](https://doi.org/10.1145/202530.202534)

`DeadStore.Prefixed` adds one native entry Store to the existing
memory diamond. The Store consumes the initial heap, and its whole
output heap enters the diamond. The guard is an evaluated Boolean.
Each Region occurrence names its own Store version within its original
arm and the intervening reader ports. The checker prepends the Store to
that arm's native table and invokes the straight-line elimination at
versions 1 and the nominated arm version plus 1. Both checks use the
entry Store's exact address port and validate concrete reader inequalities
at the given input.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Defs.lean) ·
[Straight-line verifier](sea-of-nodes-memory-dead-store.md)

Success returns a native diamond with the two checked arm bodies. The
proof uses `Merge.predecessor` and `Merge.slot` to select the corresponding
checked occurrence for each guard. The original suffix runs on the
same selected word and heap, and finite explicit-edge returns agree on
the word and entire final heap. The scope is one entry Store, one If,
and one Region in the initialized word-cell profile.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Thms.lean)

The fixture exercises both guard values in both predecessor orders.
The arms have different overwrite positions, reader ports, returned
words, and side writes. Missing the overwrite or reading the observed
cell in just one arm rejects the transformation. A separate rejection
co-locates the observed cell and a reader carried on a different port.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Regression
```
