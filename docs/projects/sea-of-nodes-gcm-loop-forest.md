# Discovering natural loops for GCM placement

Click's PLDI ’95 §2.1 computes loop nesting before scheduling, and §2.4
favors a shallow loop nest and then a low dominator-tree position.
This slice uses the established finite typed CFG inventory and
schedule-cut ranking. It computes the depth used by the ranking from
dominating CFG backedges and their natural-loop member sets.
[PLDI ’95 paper][paper] · [Archived PDF][pdf] · [Placement ranking][ranking]

## Backedge occurrences and header unions

The inventory includes the anonymous entry. The existing inventory
check requires reachable blocks and closure under every actual
successor occurrence. Discovery scans each named block once and reads
its jump, true, and false slots from the typed CFG. It retains an
occurrence if the dominator certificate places its destination above
or at its source in the tree. Parallel slots remain distinct.
`discover_sound` certifies every reported occurrence. With complete
dominator evidence, `mem_discover_iff` also certifies that every
reachable occurrence with a dominating destination is reported.
[Definitions][defs] · [Theorem header][thms]

For each discovered header, take the union of the single-backedge
member sets. Each such set consists of the header and the reachable
blocks that can reach its latch without passing through the header.
`loopHeaders_nodup` guarantees one record per header. With complete
evidence, `mem_loopHeaders_iff` and `mem_loop_iff` identify the records
and their members with exactly the semantic backedges and path sets.
[Single-backedge member proof][single] · [Theorem header][thms]

## Admitted depth and placement

The forest check requires each pair of coalesced member sets to be
disjoint or strictly nested. It rejects crossing or coincident member
sets at distinct headers. For an admitted family, depth is the number
of distinct header loops enclosing a block. With complete evidence,
`enclosing_spec` proves that the counted headers are exactly those
given by the CFG path model and that their sets form a strict inclusion
chain. [Definitions][defs] · [Theorem header][thms]

Placement passes this derived depth to the existing ranking. The cut
checker still resolves each Phi use at the exact incoming occurrence.
The ranker minimizes depth over checker-admitted cuts, then prefers
longer dominator addresses, then enumeration order. Under complete
evidence and forest admission, failure excludes every represented
legal cut. [Theorem header][thms]

The profile covers the forest of discovered natural loops. An
irreducible cycle can lack a dominating backedge and contribute no
depth. A whole-CFG nesting guarantee would
also need a certification of cyclic-region coverage or a reducibility
check. Instruction motion is outside this slice.

## Regression

The typed fixture includes an outer header with two latches, two
backedge slots at one latch, and an inner self-backedge at the other.
The outer union contributes one level. The inner latch has depth two.
Repeating the right latch in the inventory preserves the discovered
occurrence list, and omitting the left latch fails inventory validation.
The placement selector chooses the preheader for two Phi uses that
unranked discovery places at the right latch. A separate guard example
checks rejection of intersecting sets with neither set containing the
other. [Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.Regression
```

[defs]: ../../Silmaril/SSA/SeaOfNodes/GCM/LoopForest/Defs.lean
[thms]: ../../Silmaril/SSA/SeaOfNodes/GCM/LoopForest/Thms.lean
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopForest/Regression.lean
[single]: sea-of-nodes-gcm-natural-loop.md
[ranking]: sea-of-nodes-gcm-loop-placement.md
[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
