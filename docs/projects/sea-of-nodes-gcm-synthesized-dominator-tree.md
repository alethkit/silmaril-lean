# Synthesizing dominator addresses for typed GCM

Click builds the forward dominator tree in PLDI ’95 §2.1 and uses it in
early and late scheduling. The paper uses Lengauer–Tarjan. This finite
implementation uses the repository's exact structural dominance query to
find each reachable block's parent and then validates the generated
addresses with the existing certificate interface.
[PLDI ’95 paper][paper] · [Structural dominance][dominance] · [Address certifier][tree]

`immediateParent?` filters the reachable inventory to the child's strict
dominators and selects the one dominated by all of them. Dominance is
measured along finite structural entry paths in the original typed CFG.
Both slots of a conditional remain possible even when they share a target.
The proof compares common dominators by induction along an entry path.
Transitivity and antisymmetry then give an immediate parent for every
reachable named block. [Definitions][defs] · [Theorem header][theorems]

`traceAddress?` follows these parents to the anonymous entry and appends
the child indices on the way back. Each step strictly decreases the
strict-dominator count, so the length of the reachable inventory suffices.
A reachable child's final index recovers its label. The resulting address
prefixes are exact for reachable pairs, and the proposal passes the
certifier's root, uniqueness, parent-step and ancestry checks.

`synthesize?` returns the complete `DominatorTree` used by the existing
placement API. Given the injective label numbering required by that API,
`synthesize?_isSome_iff` characterizes success exactly by successor closure
of the input inventory. The numbering serves reserved addresses for
unreachable labels. Reachable indices come from the computed inventory.
The completeness proof permits cycles, parallel slots, duplicates and
unreachable labels in the inventory. [Theorem header][theorems]

The regression uses a diamond that joins at a loop header. Parallel latch
slots carry distinct Φ operands. The generated certificate accepts placement
at the header and rejects a cut in one diamond arm. It masks both an
inventoried dead block and an omitted label and rejects an inventory
missing a reachable arm. [Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[dominance]: sea-of-nodes-gcm-finite-dominance.md
[tree]: sea-of-nodes-gcm-checked-dominator-tree.md
[defs]: ../../Silmaril/SSA/SeaOfNodes/GCM/Dominance/Tree/Synthesis/Defs.lean
[theorems]: ../../Silmaril/SSA/SeaOfNodes/GCM/Dominance/Tree/Synthesis/Thms.lean
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/Dominance/Tree/Synthesis/Regression.lean
