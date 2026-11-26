# Finite saturation of guarded PEG merge obligations

This milestone implements closure for a supplied finite universe, using the
[guarded Figure 11 denotation](peg-semantics.md) and the
[E-PEG certificate kernel](peggy-epeg.md). It isolates a fixed-table
part of §4's saturation and §8's selection problem. The paper version
and artifact hash are recorded in the [PEG project notes](peggy.md).
[Paper](https://arxiv.org/pdf/1012.1802v3)

## Universe and executable closure

The universe is one typed PEG graph, an initial partition of its vertices,
and a finite list of ground merge obligations. Each obligation has a
specific pair of vertices and one of two reasons.

- A guarded equation checks that both endpoints of each declared guard
  are already in the same class. The rule client supplies a Lean proof of
  the implication from those guard stream equalities to the conclusion.
- A congruence witness binds the two actual rows to one typed label with
  its exact loop identities and ordered operands. The executable check
  compares the operand classes. Soundness uses the existing Figure 11
  equations for every legal read.

[`run`](../../Silmaril/SSA/Peggy/EPEG/Saturation/Defs.lean) scans the
current worklist for the first reason whose check succeeds and whose
endpoints are in different classes. It merges those classes using
`Classes.merge`, removes that list occurrence and repeats. It keeps
blocked reasons in the worklist, since another merge can enable them.
A run can stop when no reason is enabled or its fuel runs out. Each
unit of fuel pays for one merge. Calling `isClosed` against the
original list distinguishes a completed partition from a partial one.

`saturate` uses the list length as fuel. Every successful step
consumes one occurrence, and its conclusion stays joined by every
later step. Thus the length bound suffices even with duplicate,
blocked, or already fulfilled obligations. The implementation uses
linear scans and can revisit the same blocked reasons. Its bound
counts merges and places no guarantee on wall time.

## Guarantees

The order on partitions is inclusion of their same-class pairs.
`run_mono_fuel` proves that higher budgets preserve all pairs from a
smaller run. `saturate_extends`, `saturate_closed` and
`saturate_least` characterize the result as the least closed partition
above the seed. `saturate_mono` proves monotonicity in the seed.
`saturate_perm` proves independence of obligation order at closure.
`run_eq_saturate` gives the same result for an early run whose closure
check succeeds. The statements concern class membership. Representative
labels can depend on the order of merges.

[`run_denote_sound`](../../Silmaril/SSA/Peggy/EPEG/Saturation/Thms.lean)
uses the source's native Figure 11 solution. At every budget,
including an exhausted one, the partition satisfies the all-index
stream invariant if the seed did and the supplied guarded laws hold.
These laws quantify over entire streams, including bottom. A client
claiming correctness for more interpretations or inputs must supply
laws for each interpretation and input in that claim.

The algorithm accepts ground instances and common-label witnesses
supplied by the caller. Rule-schema matching, new vertices and newly
generated obligations require separate machinery. The least-partition
claim is for this finite table, and leaves the paper's full
node-generating saturation and termination problem open.

## Selecting a candidate

`run_selection_sound` combines any budget's sound partition with the
candidate's demand-rank and paired-root checks. Its remaining semantic
premise is a proof that the inherited source streams solve the actual
candidate's equations.

[`Selection.rows_solve`](../../Silmaril/SSA/Peggy/EPEG/Selection/Thms.lean)
can discharge that premise for same-label rewiring. Each typed row
witness binds the candidate node and its representative source node to
one label. The finite `checkRows` compares every actual candidate
operand's selected source class against the corresponding source row
operand. Agreement of the streams at all indices implies agreement of
the native equations, including the initial and feedback reads of θ
and the prefix and sampling reads of eval and pass. The rank check
still applies to the candidate table itself. The more general selection
API permits separately proved equations for candidates outside this
structural profile.

The [worked regression](../../tests/ssa/PeggyEgg.lean) saturates a ten-node
counting PEG. It revisits initially blocked θ and eval obligations,
compares all class pairs after reversing the list, and verifies an
exhausted budget is sound with an unresolved merge. The selected graph
redirects the increment from one θ to an equivalent θ, changing the
actual feedback cycle. Its row check fails before the needed class is
joined, and the completed certificate proves equality of the ordered
Figure 11 observations for the fixture's interpretation at every index.
The fixture supplies the candidate, rank and row witnesses. Candidate
search, cost metrics, global optimality and CFG reversion remain
separate obligations.

## Checks

```sh
lake build --wfail +Silmaril.SSA.Peggy.EPEG.Saturation.Thms +Silmaril.SSA.Peggy.EPEG.Selection.Thms PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker Silmaril.SSA.Peggy.EPEG.Saturation.Thms
lake env leanchecker Silmaril.SSA.Peggy.EPEG.Selection.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
