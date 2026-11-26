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

## Typed MLIR CF lowering

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Thms
```

`MLIR.lower` shares the [finite-cell body compiler](../../../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/MLIR/Finite/Defs.lean).
The fixed, initialized `Fin n → Word` heap is carried as `n` scalar `i64`
block arguments. The ordered body emits scalar scans for dynamic typed
addresses. Entry passes the initial heap to the header. The header runs
the body and forwards the returned word and updated heap to the test
block. The test emits `arith.cmpi eq` against the invariant typed stop word.
Its backedge feeds the updated heap into the header, and its other edge
passes the word and heap to exit. This is an SSA encoding of initialized,
in-bounds cells with a fixed cell count.
[CFG definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/Defs.lean)

`MLIR.lower_run_eq_some` gives the exact minimum `Cfg.run` budget of
`2 * k + 4` block ticks for a return with `k` completed backedges. `MLIR.lower_returns_iff` matches finite returns of the word and
entire heap. `MLIR.lower_denotePart` gives the corresponding observation
in the [existing partial CF evaluator](../../../../Silmaril/SSA/MLIR/CF/SwitchAssert/Denotation/Defs.lean),
and `MLIR.lower_diverges_iff` matches absence of any finite return.
[CFG theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/Thms.lean)

The emitted-CFG checks exercise the three-cell shift with zero and
two backedges, a removed store that preserves the word and changes the
final heap, and a fixed backedge with no finite return.
[CFG regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/MLIR/Regression.lean)

### Equations at typed entry valuations

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Thms
```

`MLIR.Institution.satisfaction` compares the two emitted CFGs using
the canonical scalar profile at the native model's cell count. It
preserves and reflects agreement on every initial heap, including
the absence of a finite return. `observe_mapGraph` and
`satisfaction_reindex` relate re-emission after a typed entry port map
to pullback of the native valuation, with the same heap and cell count.
These laws compare observations of generated CFGs over the existing
native models.
[Native institution](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Thms.lean) ·
[MLIR equation theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/Institution/Thms.lean)

### Compare emitted backend observations

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Thms
```

At a shared typed entry valuation and initial heap,
`lambda_observation_iff_mlir` identifies the λSSA return at label zero
with the CF observation of its packed word and whole final heap.
`mlir_observation_eq_map_theta` re-encodes the numbered θ result by
reading its word and heap wires into the scalar CF result tuple.
`mlir_observation_iff_run` connects that partial CF observation to
finite execution of the emitted CFG.
[Backend comparison](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Thms.lean)

`lambda_no_return_iff_mlir` and `theta_no_return_iff_mlir` match
absence of finite returns. The corresponding satisfaction laws
compare equations over all initial heaps at the chosen valuation.
The regression checks the three-cell result after two backedges
and the absence of a result in all three backends on a fixed backedge.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Regression.lean)

The CF evaluator runs scalar bindings with a total bitvector
interpretation. The LLVM scalar profile rejects `llvm.load`.
The MLIR result in these laws uses the initialized cells carried
as SSA values above.
[CF evaluator](../../../../Silmaril/SSA/MLIR/CF/Basic/Defs.lean) ·
[LLVM admission example](../../../../Silmaril/SSA/MLIR/LLVM/Examples/Thms.lean)
