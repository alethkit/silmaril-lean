# Checking dominator addresses for typed GCM

Click uses the forward dominator tree to constrain early and late scheduling
and to break placement ties in PLDI ’95 §§2.1–2.4. This adapter turns proposed
tree addresses into the existing GCM `DominatorTree` certificate. It uses the
typed CFG directly, including the source slot of every branch occurrence.
[PLDI ’95 paper][paper] · [GCM legality][legality]

Supply a successor-closed finite inventory and proposed root-to-block
addresses. The checker computes reachability with the existing traversal,
then compares address-prefix ancestry with the certified dominance query
for every reachable pair. The entry has the empty address. Each other
reachable block extends a reachable parent's address by one element, and
reachable addresses are distinct. Address elements are tree indices. A tree
edge can span several CFG edges.
[Definitions][defs] · [Structural dominance][dominance]

The existing certificate interface requires address injectivity on the entire
typed label domain. The adapter accepts an injective numbering of those
labels, including the anonymous entry. It uses the numbering only to give
unreachable labels distinct addresses starting with zero. Reachable addresses
use positive elements, preserving their prefix relation and lengths.
`prefix_iff_dominates` proves exact ancestry for every reachable target,
even if the proposed ancestor is outside the inventory. `parent_address`
proves the one-step address property, and `immediate_dominator` identifies
the parent by its structural dominance property. [Theorems][theorems]

`certify?` returns a complete tree on the original CFG for use by
`checkPlacement` and the other tree-based GCM APIs. The adapter validates a
supplied proposal. Tree synthesis is a separate problem.

The fixture joins a diamond at a loop header with two parallel latch
backedges carrying different operands. It checks both arms against the join
and passes both Φ reads through the existing placement checker. An
inventoried dead block and an omitted label remain unreachable. The checker
rejects a false ancestor claim, a skipped parent level, and an inventory
with a missing reachable arm. [Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[legality]: sea-of-nodes-gcm-legality.md
[dominance]: sea-of-nodes-gcm-finite-dominance.md
[defs]: ../../Silmaril/SSA/SeaOfNodes/GCM/Dominance/Tree/Defs.lean
[theorems]: ../../Silmaril/SSA/SeaOfNodes/GCM/Dominance/Tree/Thms.lean
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/Dominance/Tree/Regression.lean
