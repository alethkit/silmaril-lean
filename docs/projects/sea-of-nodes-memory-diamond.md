# Sea of Nodes memory diamond

IR ’95 §2.5 treats the whole STORE as an SSA value that a Phi can merge.
Section 3.1 describes a Phi latching the operand paired with the arriving
Region input. Simple chapter 10 illustrates both with
`if (arg) p.x = 3; else p.x = 4; return p.x;`. The post-join load consumes the
memory selected by the Region.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Simple chapter 10 at `f0a6c675`](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

The graph takes an evaluated Boolean guard. It uses the existing control
diamond's If projections and two Region positions, and the straight-line
memory graph for each arm and the common suffix. Each arm's Return exports a
word and its last memory version. Only the executed arm publishes on its
incoming edge. The Region latches the pair at the matching slot, so either
predecessor order is legal. The suffix receives that heap as its Start
version and the selected word as an extra argument. Region slots distinguish
the incoming occurrences even though both edges enter the same Region.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/Defs.lean) ·
[Memory profile](sea-of-nodes-memory.md)

Import `Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms` for
`Graph.returns_iff_denote`. It equates finite execution through the explicit
control and memory edges with the heap-threaded denotation on both the
returned word and the entire final heap. `latch_publish_iff` characterizes
successful latching by the arriving slot and the payload, including when
used on a heap alone. Each executed table keeps its declared effect order.
The profile has total access to initialized word cells and covers one If and
one join. Alias analysis, exceptions, loops, and schedule changes are outside
the scope.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/Thms.lean)

The regression evaluates both guards in both predecessor orders. Each arm
saves the old value of the same cell into its own distinct cell, then
overwrites the shared cell with a different word. The suffix loads the shared
cell. The checks cover the returned word, the whole final heap, the untouched
cell of the untaken arm, and rejection at the wrong Region slot.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Regression
```

## Native equations

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
```

The native `inst` uses ordered lists of address and word ports as
signatures. A signature map sends each source input port to a target port
of the same sort. This allows a rename to redirect a Load or Store to a
different address input. Load, Store, Return, and the Boolean branch rule
have their fixed meanings throughout. `mapGraph` preserves the memory
producer indices and Region predecessor order. Its suffix map also keeps
the selected arm's exported word at the first port.

A model supplies a cell count and a typed valuation of the scalar entry
ports. Its reduct looks up those ports along the signature map. At that
valuation, an equation compares both components of `Model.observe` for
every Boolean guard and every initial heap. `Model.returns_iff_observe`
relates this pair to the occurrence-indexed execution rules above.
`returns_mapGraph` gives the pointwise reindexing law for these rules, and
`Equation.satisfaction` gives the institution's satisfaction condition.
These results use the initialized-cell profile described above.
[Institution API](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/Institution/Thms.lean)

The institution regression swaps two address ports. It checks an equation
that changes only the predecessor order and an equation that removes a
taken store. The second equation returns equal words on both sides.
A changed cell in the final heap falsifies it.
[Institution regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/Institution/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Institution.Regression'
```
