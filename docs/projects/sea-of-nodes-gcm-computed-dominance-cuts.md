# GCM cut discovery using typed CFG dominance

Click uses dominance to constrain early and late scheduling in PLDI ’95
§§2.2–2.3. Here the constraints are checked over candidate cuts in the
existing typed CFG. The caller supplies operand cuts, uses and a finite
block inventory with decidable typed label equality. The checker computes
reachability and dominance from the CFG. [PLDI ’95 paper][paper] ·
[Executable structural dominance][dominance]

`checkCut` checks successor closure, then uses the same placement check
over operands and resolved uses as the tree-based API. A cut must be in
bounds in a reachable block. Availability requires structural dominance
and, when the read shares a block with the definition, the local cut
order. A Φ use resolves to its source terminator using the exact
successor slot and argument index. Parallel occurrences share a read
position when they leave the same terminator. [Definitions][defs] ·
[Original cut checker][legality]

`checkCut_iff` equates success with closure and the existing `Legal`
predicate. `discoverCut` selects the first accepted cut from the existing
enumeration. `discoverCut_sound` certifies the selected cut. With closure,
`discoverCut_eq_none_iff` rules out all legal cuts of the typed CFG because
every reachable block occurs in the inventory and all its in-bounds cuts
are enumerated. The result concerns legal placement. Loop-depth ranking
and program transformation have their own APIs. [Theorems][theorems]

The diamond regression includes two parallel Φ inputs at one arm's
terminator and an ordinary read at the join. It accepts an arm-local cut
for both Φ uses, rejects the cut before that arm's operand, and requires
the entry cut when the join read must also be served. It rejects a nonexistent
jump occurrence and an inventory missing a reachable arm. [Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Placement.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Placement.Correctness
```

[paper]: https://doi.org/10.1145/207110.207154
[dominance]: sea-of-nodes-gcm-finite-dominance.md
[legality]: sea-of-nodes-gcm-legality.md
[defs]: ../../Silmaril/SSA/SeaOfNodes/GCM/Dominance/Placement/Defs.lean
[theorems]: ../../Silmaril/SSA/SeaOfNodes/GCM/Dominance/Placement/Thms.lean
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/Dominance/Placement/Regression.lean
