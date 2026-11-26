# Delete a Store overwritten within a memory loop activation

Simple chapter 10 deletes a Store overwritten at the same pointer and
field when the earlier Store has no other memory users. Its loop
example closes the memory Φ with the activation's final memory version.
This increment applies the local deletion to the admitted ordered memory
loop, whose entire body executes before the tail test.
[Pinned Simple StoreNode rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[Pinned Simple memory Φ](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable) ·
[IR ’95 §§2.5 and 3.1–3.2](https://doi.org/10.1145/202530.202534)

`Memory.Loop.DeadStore.rewriteWith` takes two one-based Store versions
in the original activation table and a typed disjoint-address
certificate. The straight-line checker requires a later Store to the
same original address port before the body's Return. It checks every
intervening Load against the certificate and reconnects the surviving
memory chain. `rewrite` checks the concrete inequalities on the
invariant input tuple, and the resulting body must still admit a native
`Loop.Graph`.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/DeadStore/Defs.lean) ·
[Straight-line verifier](sea-of-nodes-memory-dead-store.md)

The checked body exports the same test word and heap from every
latched heap under a satisfying input. Hence each activation exits
with the same observation or takes a backedge with the same heap.
The native evaluator agrees at every exact backedge count, and
explicit-edge finite returns agree on the word and whole final heap.
The scope is one unconditional overwrite within the same activation
of a tail-tested loop over initialized cells.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/DeadStore/Thms.lean)

The fixture checks both repeated activation and a zero-backedge exit.
The disjoint read loads a word used by the overwrite. When its port
aliases the deleted Store's cell, deletion would change the next
heap, and the invocation check rejects. A same-wire read, an overwrite
to the wrong cell, and a missing overwrite also reject.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/DeadStore/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.DeadStore.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.DeadStore.Regression
```
