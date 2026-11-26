# Forward a Load through a memory loop backedge

Simple chapter 10 pushes a Load of a memory Φ onto the incoming edges.
For a loop it checks that the backedge Load folds against a matching
Store. This increment implements that case for the first Load of a
native tail-tested `Memory.Loop.Graph`, with one captured address and
ordered, initialized word cells. The incoming memory follows IR ’95’s
STORE dependencies and Region/Phi convention.
[Pinned Simple `LoadNode.idealize`](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/LoadNode.java#L58-L88) ·
[IR ’95 §§2.5, 3.1–3.2](https://doi.org/10.1145/202530.202534)

`Carried.rewrite` selects the last Store and checks that it targets the
first Load’s captured address. `Carried.rewriteWith` takes a one-based
Store version and an existing `Disjoint.Certificate`. The nominated
Store must use the captured address wire. Every later Store must use a
covered writer port distinct from that wire. The certificate requires
that the captured cell and each listed writer’s concrete cell be
unequal. `rewriteChecked` checks those inequalities at the invocation.
The first Load sees version zero, and all remaining effects keep their
table order.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Carried/Defs.lean) ·
[Disjoint certificate](../../Silmaril/SSA/SeaOfNodes/Memory/Forwarding/Disjoint/Thms.lean)

The target’s entry table performs one Load and exports it with the
initial heap. The target body is the original typed suffix
`Memory.Body args [[.word]] 0`, whose first local is now the scalar Φ
operand. A single execution evaluates each Store’s typed data wire once.
It saves the nominated operand at the write and carries it unchanged
through the remaining effects. The guard and exit still use the native
Return wire. `seed_agrees` establishes the cached-cell invariant at
entry. `rewriteWith_stored_reads` ties the actual Store word to the
captured cell after the suffix. On every input satisfying the certificate,
the exact-backedge and finite-return theorems preserve the returned word
and entire final heap.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Carried/Thms.lean)

The same-wire fixture logs the entry value and changing carried words,
including an exit at zero backedges. The separate-wire fixture tests
words 1 and 2 on successive backedges while carrying Store words 2 and
0. Its exit returns 0 with 2 in the captured cell. A final Store to a
different port is rejected even after an earlier matching Store.
The certified suffix fixture adds a fifth Store that writes the guard
word to a distinct logging cell while the fourth Store supplies feedback.
The checker rejects an uncovered writer and an invocation where the
logging port aliases the captured cell.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Forwarding/Carried/Regression.lean)

## Discover the latest Store

`Carried.Search.discover` reads the first Load’s captured address port
and walks Store occurrences from newest to oldest. It chooses the first
Store with that exact port and collects every newer Store’s original
writer port in the same order. A newer writer outside the typed argument
profile blocks discovery. The existing suffix checker validates the
selection before returning the graph and its certificate.
[Search definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Carried/Search/Defs.lean)

`discover_latest` identifies the actual Store occurrence and the complete
suffix. It proves port distinctness. `discoverChecked` checks concrete
cell inequality separately for each invocation. The exact-backedge and
finite-return theorems reuse the certified suffix proof under those
inequalities.
[Search theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Carried/Search/Thms.lean)

The discovery fixture selects Store 3 over Store 1 and keeps Store 4’s
logging effect. It completes two backedges with the whole heap checked.
The same graph rejects an invocation where log aliases head. A second
graph has only a Store to another port and yields no candidate.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Forwarding/Carried/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Thms
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Regression
```
