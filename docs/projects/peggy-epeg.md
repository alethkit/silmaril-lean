# Guarded cyclic E-PEG certificates

The [certificate kernel](../../Silmaril/SSA/Peggy/EPEG/Thms.lean) uses
the [guarded Figure 11 semantics](peg-semantics.md) on a fixed typed PEG
table with a fixed loop frame. The table may contain graph cycles, since
well-foundedness is on requests (vertex and full iteration vector).
For ranked loop-free graphs, the [Egg bridge](peggy-egg.md) instead
replays sorted term explanations and relates their results to the same
native observations.

## Class equality and merges

`Classes.Valid classes values` says that two vertices with the same
finite class label have the same declared sort and equal partial
values at every iteration vector, including bottom. Here `values`
can be the guarded solution for a particular interpretation and input.
`Classes.discrete_valid` starts the partition with singleton classes.
`Classes.merge` replaces the entire right class label by the left's.
`Classes.merge_sound` needs an independently justified stream equality
for that pair and preserves the invariant for the whole new partition.

`GuardedEquation.check` checks each ground guard against the current
partition. The caller supplies a Lean proof of
`GuardedEquation.Holds` for the valuation, meaning that agreement of
all guard streams entails agreement of the conclusion streams.
`GuardedEquation.merge_sound` uses the invariant to justify the checked
guards before applying that law. A guard known at only one index cannot
supply this premise. Clients seeking a uniform optimization theorem
must supply the laws for every interpretation and input they claim.

`MatchingNodes` binds both original node rows to the same typed
label, including its loop identity, and to their actual ordered
operand references. Lean checks those bindings.
`MatchingNodes.checkOperands` compares the operand classes.
`MatchingNodes.merge_sound` uses the graph equations and agreement of
the operand streams. Its proof compares each read under the exact
`Label.kind` and `EdgeKind.Changes` constraints:

- θ compares the initial slot at index zero and the feedback slot at
  the preceding count in the same loop coordinate.
- Eval compares the count slot at the original vector and the sample
  slot at the selected count and every earlier prefix count in that
  coordinate.
- Pass compares the predicate stream at every sample in that
  coordinate, which also agrees on least eligible true and bottom.
- Primitive and φ operands keep the original vector and their ordered
  slots. The native equation determines strictness and arm selection.

Proof-producing rule search, arbitrary node extension, saturation,
and inference of mutually recursive stream equalities remain separate
obligations. In particular, congruence uses equalities already justified
by the current partition, so it cannot assume the conclusion of the
merge it is checking.

## Checking a proposed selection

A `Selection` names one typed source representative for every vertex
of the actual candidate table. Both graphs have the same ordered
parameter and result interfaces and the same index frame. Its
executable `check` runs the candidate's own `DemandRank.check` and
checks each candidate root representative against the corresponding
source root class. Demand rank is the native admission route used by
this checker. The paper's separate structural scope condition can
be imposed by a client that needs it.

`Selection.inherit` assigns each candidate vertex its representative's
entire native stream. `Selection.observe_sound` additionally requires
a Lean proof that this assignment solves **every** candidate node
equation. It obtains well-founded demands from the executable check
and uses native solution uniqueness to prove equality of the complete
ordered output tuple at every index. A finite rank or root class check
alone supplies no satisfaction proof.

A future extractor can produce the candidate, the representative
assignment, and certificates for its equations, and reuse this
theorem. Reversion to control flow requires its own scope and
observation theorem. Selection search and cost guarantees are outside
the certificate kernel. The observation retains partial values in
order and has the same failure and effect boundaries as Figure 11.

## Checks

```sh
lake build --wfail +Silmaril.SSA.Peggy.EPEG.Thms PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker Silmaril.SSA.Peggy.EPEG.Defs
lake env leanchecker Silmaril.Proofs.SSA.Peggy.EPEG.Sound
lake env leanchecker Silmaril.SSA.Peggy.EPEG.Thms
lake env leanchecker tests.ssa.PeggyEgg
```

The [cyclic fixture](../../tests/ssa/PeggyEgg.lean) contains a real θ
feedback cycle. It replays congruence for duplicate seeds, pass and
eval, and a guarded θ merge. It checks equality for a selection with
different ordered root references, rejects a same-index initializer
cycle, and proves that a candidate can pass both finite checks and
still violate its inherited equations. `PeggyEggTests` is part of
`make check`.
