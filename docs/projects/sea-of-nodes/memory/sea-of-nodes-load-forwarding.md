# Checked Load forwarding in Sea of Nodes memory

`Forwarding.rewrite` takes a one-based Store version and a zero-based Load
position in the original table of Loads and Stores. It accepts when the
Load's memory producer is that Store and both address operands are the same
argument port. The scanner tracks the latest Store. Any intervening Store
publishes a new version and replaces that tracked producer, even for a
write to the same address. Intervening Loads preserve the version.
[Definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Forwarding/Defs.lean) ·
[Source memory edges](sea-of-nodes-memory.md)

On acceptance, the rewrite removes the selected Load and substitutes the
Store's word origin for all uses of the Load result in the suffix. Other
scalar origins are reindexed, and all Stores remain in their original order.
The Lean theorem preserves and reflects the operational observation of both
the returned word and exact final heap. Its proof uses the source theorem
relating explicit memory snapshots to the current-heap denotation.
[Theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Forwarding/Thms.lean)

This corresponds to Simple chapter 10's rule for a Load whose memory input
is directly a matching Store. IR ’95 §2.5 and Figure 6 give the memory
dependence, and §5.1 describes local graph optimization. The profile uses
total reads of initialized word cells. Its address check uses argument
identity. Inferring equality between different address expressions and
forwarding past other Stores require additional proofs.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Simple chapter 10 LoadNode](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/LoadNode.java#L55-L62)

The regression forwards through an intervening Load and redirects later
Store and Return operands. It rejects a candidate for the first Store when
a same-address overwrite produced the selected Load's version, then accepts
the actual producer. [Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Forwarding/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Regression
```
