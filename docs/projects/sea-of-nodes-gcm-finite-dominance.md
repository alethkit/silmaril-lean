# Structural dominance on a finite typed CFG

Click uses the forward dominator tree to bound early and late scheduling in
PLDI ’95 §§2.1–2.4. This slice computes the underlying block dominance
relation on the typed CFG used by the GCM cut checker.
[PLDI ’95 paper][paper] · [Archived PDF][pdf] · [GCM cut checker][legality]

The caller supplies a finite list of typed block labels with decidable equality.
`checkClosed` checks every successor of the anonymous entry and every
listed block, including unreachable blocks in the list. The inventory may
contain duplicates. By `path_endpoint_mem`, a closed inventory covers every
endpoint of an actual structural entry path. Both conditional arms can occur
on these paths regardless of the run-time condition.

`occurrences` projects the jump, true and false slots of the typed terminator.
`mem_occurrences_iff` identifies each projected pair with its exact source
slot and typed destination. Parallel branches keep their distinct slots,
which the cut checker uses to identify incoming Φ arguments. Reachability
only asks whether at least one slot connects a pair of vertices.
[Definitions][defs] · [Theorems][thms]

`dominates? cfg blocks a b` requires a closed inventory and a reachable
`b`, then checks that deleting `a` prevents a path to `b`. The traversal starts
at the entry if it is kept and adds one eligible successor per successful
step. Each step removes at least one candidate, so the length of the
filtered inventory suffices as fuel, even with duplicates.
`reachesKeeping?_iff` proves exactness for paths whose vertices all satisfy
the filter. `dominates?_iff` proves that the query succeeds exactly when the
inventory is closed, `b` is reachable and every structural entry path to
`b` visits `a`. This includes cycles and excludes vacuous dominance of
unreachable blocks.

The deletion criterion also underlies the repository's numeric dominator
solver in Machine. The typed implementation reuses the SSA natural-loop
closure proof, with adjacency reversed for forward traversal. This keeps
the SSA dependency boundary. The result is a Boolean relation. The
cut discovery API can use it directly. Consumers of `DominatorTree`
still require certified tree addresses. [Numeric solver][numeric] ·
[SSA closure proof][closure] · [Dependency map][regions] · [Cut discovery][cuts]

The executable regressions cover a diamond join, an incomplete inventory,
and a loop with two latch slots that both target the header and carry
different arguments. A dead block in the loop inventory has a different
parameter list and an edge to the exit. It stays unreachable and contributes
no dominance facts. [Regressions][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.Dominance.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.Dominance.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Correctness
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Regression
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[legality]: sea-of-nodes-gcm-legality.md
[defs]: ../../Silmaril/SSA/SeaOfNodes/GCM/Dominance/Defs.lean
[thms]: ../../Silmaril/SSA/SeaOfNodes/GCM/Dominance/Thms.lean
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/Dominance/Regression.lean
[numeric]: ../../Silmaril/Raw/Machine/CBackend/Graph/Dominance.lean
[closure]: ../../Silmaril/SSA/SeaOfNodes/GCM/NaturalLoop/Thms.lean
[regions]: ../../regions.toml
[cuts]: sea-of-nodes-gcm-computed-dominance-cuts.md
