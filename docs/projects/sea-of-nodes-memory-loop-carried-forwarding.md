# Forward a Load through a memory loop backedge

Simple chapter 10 pushes a Load of a memory Φ onto the incoming edges.
For a loop it checks that the backedge Load folds against a matching
Store. This increment implements that case for the first Load of a
native tail-tested `Memory.Loop.Graph`, with one captured address and
ordered, initialized word cells. The incoming memory follows IR ’95’s
STORE dependencies and Region/Phi convention.
[Pinned Simple `LoadNode.idealize`](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/LoadNode.java#L58-L88) ·
[IR ’95 §§2.5, 3.1–3.2](https://doi.org/10.1145/202530.202534)

`Carried.rewrite` checks that the last Store targets the first Load’s
original address argument. Each Store supersedes the previous address
match, so an earlier matching write gives no evidence about the final
memory version. The first Load sees version zero and all remaining
effects keep their table order. The captured arguments are fixed
throughout the run. The check compares typed wires and any earlier
aliasing Stores precede the checked write.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Carried/Defs.lean)

The target’s entry table performs one Load and exports it with the
initial heap. The target body is the original typed suffix
`Memory.Body args [[.word]] 0`, whose first local is now the scalar Φ
operand. A single execution of the suffix evaluates each Store’s typed
data wire once and keeps its word for feedback. The guard and exit still
use the native Return wire. `seed_agrees` establishes the cached-cell
invariant at entry. `rewrite_lastStored_reads` ties the actual Store word
to the addressed cell of the final heap, and `rewrite_step_agrees` uses
it to reestablish the invariant on feedback. The exact-backedge and
finite-return theorems quantify over every typed input, initial heap,
and entire final heap.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Carried/Thms.lean)

The same-wire fixture logs the entry value and changing carried words,
including an exit at zero backedges. The separate-wire fixture tests
words 1 and 2 on successive backedges while carrying Store words 2 and
0. Its exit returns 0 with 2 in the captured cell. A final Store to a
different port is rejected even after an earlier matching Store.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Forwarding/Carried/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Regression
```
