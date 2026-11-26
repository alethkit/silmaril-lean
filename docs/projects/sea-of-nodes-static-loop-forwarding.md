# Static forwarding with typed address facts

`Static.rewrite` takes the native memory loop and the nominated Store
version and Load index. It produces one optimized `Loop.Graph` and a
finite list of address facts before any input values are supplied.
The first scan reads the selected Load's original address port and records
the writer ports strictly between the nominated Store and that Load.
A write to the very same port makes the pass reject. The existing
straight-line checker verifies that the nominated Store has the Load's
original address port and reindexes the scalar uses. The loop wrapper
checks the rewritten body still contains a Load and a Store.
[Static definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Static/Defs.lean) ·
[Loop forwarding](sea-of-nodes-memory-loop-forwarding.md) ·
[Disjoint Store scan](sea-of-nodes-disjoint-load-forwarding.md)

Each reported fact requires the Load's address and a named writer's address
to be unequal as concrete `Fin cells` values. Ports identify the arguments
whose values must be compared. `facts.Valid input` is the input contract,
and the existing `Certificate.check` decides it at a given valuation.
`rewrite_checked` relates the one static result to the checked rewrite
at every admissible valuation. The preservation theorems cover the
activation's word and full heap, the feedback or exit transition, exact
backedge counts, and finite returns for every initial heap.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Static/Thms.lean)

The fixture uses the same static graph at two valuations. One completes
two backedges with separate scratch and logging cells. The other exits
at zero backedges with scratch and logging sharing a cell, since that
logging Store follows the Load. A third valuation aliases scratch with
the intervening head Store, violates the facts, and exhibits different
body words. The scope is same-activation forwarding for typed address
arguments in the ordered, initialized word-cell profile.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Forwarding/Regression.lean)

The address obligations concern the Store dependencies from IR ’95 §2.5
and use the source loop latch of §§3.1–3.2. Simple chapter 10 describes
local folding at a matching Store and checking for conflicting writes.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Pinned Simple chapter 10](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#local-memory-optimizations)

## Discovering a pair

`Static.Search.rewrite graph` visits Loads by increasing original table
index, counting both Loads and Stores from zero. At each Load it tries the
preceding Stores by decreasing one-based Store version. It returns the
first graph and facts accepted by `Static.rewrite`, or `none` if every
pair fails. `rewrite_eq_some_iff` states the first-success order.
`facts.Valid input` still requires actual cell inequality at the input.
[Search definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Static/Search/Defs.lean) ·
[Search theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Static/Search/Thms.lean)

One fixture picks the newer of two scratch writes across a tail write,
with scratch and tail required to name distinct cells. A later Load also
has an accepted pair. A loop whose only Load would be removed has no
admitted pair. The feedback fixture exercises a full-heap return at zero
and two backedges through the search API.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Forwarding/Regression.lean)

This is a search for the local Load-after-Store fold in Simple chapter 10,
using IR ’95 §2.5's explicit memory dependencies. Store numbering starts
afresh on each activation. The incoming memory Φ supplies the whole heap
as version zero. Forwarding from a previous activation would require a
loop-carried store fact and an entry-case proof.
[Pinned Simple LoadNode](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/LoadNode.java#L55-L62) ·
[IR ’95](https://doi.org/10.1145/202530.202534)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Search.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Thms
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Thms
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Search.Defs
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Search.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Regression
```
