# Numbered RVSDG θ for a Sea of Nodes memory loop

One numbered θ vertex runs the source loop's ordered memory table and
then tests the word it exported. The body reuses the straight-line memory
lowering, with a pure tag vertex appended at its return wires. The tag
vertex reads the table's final heap and forwards it unchanged. Tag zero
returns the updated heap and tag one supplies that same heap to the next
activation. The carrier has the original scalar arguments and one explicit
heap state port. The exit reads the invariant stop word from the carrier,
which equals the actual body word on every stop.
[Source memory loop](sea-of-nodes-memory-loop.md) ·
[Ordered memory lowering](sea-of-nodes-memory-rvsdg.md) ·
[Target definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Theta/Defs.lean)

The boundary follows IR ’95 §§2.5 and 3.1–3.2 and Figure 7. Start supplies
the entry heap and the completed activation supplies the backedge heap.
Simple chapter 10 gives the whole-memory Phi example with a header test.
This fragment uses the paper's tail test. The first θ activation is
mandatory, so zero source backedges still run every body effect.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Pinned Simple chapter 10](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

`Graph.lowerTheta_returns_iff` preserves and reflects the returned word
and entire final heap against the numbered evaluator.
`Graph.lowerTheta_returnsAfter_iff` relates exactly `n` completed source
backedges to success at `n + 1` target activations and absence of a return
at `n`. The target consumes one unit of fuel for the final activation.
The shared regression reduces the numbered graph at the two-activation
bound and checks the three-activation observation through the exact
correspondence theorem. A second fixture repeatedly loads and stores
the same value, forcing another activation at every bound.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Theta/Thms.lean) ·
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Theta/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Theta.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Theta.Activation
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Theta.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Theta.Regression
```
