# Sea of Nodes tail-tested memory loop

IR ’95 §2.5 models the whole STORE as an SSA value that a Phi can merge.
Sections 3.1–3.2 and Figure 7 show a Loop Region latching by the arriving
control occurrence, with a tail If whose true projection goes back to
the header. Simple chapter 10 closes a loop's memory Phi with the memory
produced in the body. Its example uses a header test. This fragment uses
the paper's tail test and the same occurrence-to-memory correspondence.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Simple chapter 10 at `f0a6c675`](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

The entry occurrence selects Start's initialized heap. The backedge
occurrence selects the preceding activation's final memory version. The
selected heap is memory version zero for the next activation's ordered
straight-line table. Each table contains a Load and a Store. The word
it exports is the tail If's data input. Comparing it to a typed invariant
word argument determines exit on equality and a backedge otherwise. The
exit observes that word and the latest heap. Zero backedges still execute
the table once.
[Definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Defs.lean) ·
[Straight-line memory profile](sea-of-nodes-memory.md)

Import `Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms` for
`Graph.returns_iff_mem_denote`. It identifies finite explicit-edge returns
with membership in the heap-threaded partial denotation, observing the
word and whole final heap. `Graph.returnsAfter_iff_evalAfter` adds an exact
completed-backedge count. The executable `evalAfter` yields `none` when
there is no return at that count. The model fixes the table's effect order
and uses already initialized word cells. It covers one header and one
backedge with a total body and total test.
[Theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Thms.lean)

The regression shifts one initialized cell into another and clears the
source cell. The one-activation case still performs both stores. In the
two-backedge case the first activation loads `1` and writes `2` to the same
address. The next activation loads that `2`, and the third loads `0` and
exits. The checks observe the entire final heap and its untouched cell.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression
```
