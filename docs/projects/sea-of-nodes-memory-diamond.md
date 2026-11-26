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

## Two initialized cells in typed MLIR CF

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Thms
```

`MLIR.lower` compiles the native memory diamond at `Heap 2` to the
repository's typed `MLIR.CF.Cfg`. Entry receives an `i1` Boolean guard,
two `i64` cell values, and the original scalar arguments. Each
`Fin 2` address is an `i1`. A Load uses one scalar `arith.select` to
read the addressed cell. A Store uses two selects to form the new cell
values, changing only the addressed one. Every Load and Store in the
ordered native arms and suffix is supported at this boundary.

The entry's `cf.cond_br` goes to the block for the selected predecessor
occurrence. Each arm branches to the join with three `i64` operands:
the exported word, cell zero, and cell one. The shared suffix can use
these arguments and the dominating scalar inputs. The return tuple
contains the suffix's word and both final cell values.
[Typed CF evaluator](../../Silmaril/SSA/MLIR/CF/Basic/Defs.lean) ·
[Lowering](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/MLIR/Defs.lean)

`lower_run` proves that the existing evaluator returns that tuple at
every budget of at least three blocks. `returns_iff` preserves and
reflects the native relation for both guards, with the two output cells
determining the entire final heap. The profile uses scalar SSA state
values and the fixed-width interpretation of `arith.select`. It covers
total access to two initialized cells.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/MLIR/Thms.lean)

The regression runs the emitted CFGs for both guards and both
predecessor orders. It checks equal returned words with different
heaps, rejects the heap from an omitted store, and executes a suffix
that uses the selected export and updated heap.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/MLIR/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.MLIR.Regression'
```

### Two-cell equations

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.Thms
```

`translateEquation` keeps both emitted CFGs with their own predecessor
orders. The canonical observation is the word and both final cells from
the existing evaluator at a three-block budget. At a two-cell typed
valuation, `translated_satisfaction` equates the compiled sentence's
truth with native satisfaction for all guards and initial heaps.
`behavior_mapGraph` and `satisfaction_reindex` relate re-emission after a
typed port map to pullback of the entry valuation.
[Equation API](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/MLIR/Institution/Thms.lean)

`validity_two_cells` quantifies that satisfaction law over all typed
valuations at cell count two. Native validity quantifies over every
cell count. The regression separates them by reversing two swaps
that share an address. The two orders agree on two cells for every
valuation, and a valuation with three distinct addresses gives
different final heaps.

`MLIR.Institution.Backends.Thms` relates the same encoded return to
the existing λSSA return observation and numbered RVSDG γ tuple. Its
equation theorems compose with the corresponding backend satisfaction
laws at the same two-cell valuation.
[Backend API](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/MLIR/Institution/Backends/Thms.lean) ·
[Equation regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/MLIR/Institution/Regression.lean)
