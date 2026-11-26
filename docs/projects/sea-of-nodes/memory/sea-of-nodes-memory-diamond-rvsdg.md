# Ordered RVSDG lowering of a Sea of Nodes memory diamond

The source exposes the arriving Region occurrence, the returned word, and
the final whole-memory value. IR ’95 describes these memory values and the
Phi latch in §§2.5 and 3.1. The fixture follows Simple chapter 10's
conditional writes to one address and load after the join.
[Source diamond](sea-of-nodes-memory-diamond.md) ·
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Pinned Simple chapter 10](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

The target is one ordinary acyclic RVSDG γ followed by the straight-line
suffix. Its entry takes the already evaluated guard encoded as the
zero-based Region slot, the original scalar arguments, and one heap.
Children are numbered in Region order. The γ passes the original arguments
and the single heap into the selected child. Its result contains the
selected word and heap. The suffix reads the word from that result, keeps
the original scalar arguments in scope, and takes its live runtime from the
same γ result.
[Definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/RVSDG/Defs.lean)

Both children and the suffix use the same ordered lowering and
`StateM (Heap cells)` leaf model. `Body.lowerAt` admits a typed scalar
routing and a live heap wire in the enclosing region. Its proof relates
that use of the lowerer to the source fold. `Graph.lowerChecked` witnesses
the canonical single-runtime check on the numbered graph.
[Straight-line lowering](sea-of-nodes-memory-rvsdg.md)

Import `Silmaril.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Thms` for
`Graph.lower_run_selected`. The numbered RVSDG evaluator runs the
selected child, then the suffix starting from that child's full output.
`Graph.lower_returns_iff` preserves and reflects both the returned word
and the entire final heap against the source finite execution relation.
The lowering fixes the declared order of Loads and Stores on initialized
word cells. The contract covers one If and one join.
[Theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/RVSDG/Thms.lean)

The regression runs the numbered graph directly on the source fixture
with each guard under both predecessor orders. It compares both outputs
and inspects the untaken arm's cell under reversed order. A second suffix
returns the saved word directly from the γ data port.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/RVSDG/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.RVSDG.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.RVSDG.Regression
```
