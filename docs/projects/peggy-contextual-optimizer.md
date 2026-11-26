# Contextual PEG rewrites and ordered output validation

[`Optimizer.Contextual.Thms`](../../Silmaril/SSA/Peggy/Optimizer/Contextual/Thms.lean)
checks internal rewrites in ranked, loop-free PEGs with a fixed ordered
parameter and result interface. It preserves the Figure 11 observation
as a tuple of partial values. The
[single-result root optimizer](peggy-optimizer.md) retains its existing
entry points and unfolded application metric.

## Discovery and replay

The contextual optimizer scans the vertices reachable from any output.
A table may contain schemas at different conclusion sorts. At each
site of the schema's sort, the shared matcher enumerates typed vertex
bindings and compares the instantiated left side to the exact unfolded
site term. Repeated variables retain one binding. A right side still
constructs one primitive or φ application with variable operands.

The generator replaces that one row at its current address. All incoming
references keep pointing to it, including repeated uses and uses from
different outputs. The rest of the table and the ordered roots retain
their addresses. The checker tests every row of the candidate against
the original rank, which rules out self-dependence and larger-rank
dependencies. This can conservatively reject candidates that would
admit a different rank.

`receiptAt` walks the old graph by its rank. Each occurrence of the
chosen address receives the matched rule receipt, and every unchanged
application combines its children's receipts with
`Core.Replay.Receipt.congr`. The producer gives one such receipt per
output. Replay checks each proof against the actual old and new roots
in order. Guard receipts propose reflexivity and replay checks the
instantiated guard endpoints. The supplied rule laws still quantify over
partial values. Proofs requiring a nonreflexive guard need a separately
supplied receipt through the general output validator.

Walking both arms of a φ constructs syntax and evidence. The matcher,
generator, rank check and replay have no primitive interpretation and
perform no evaluation. `CheckedProgram.sound` applies the proved
Figure 11 bridge, including strict primitives, undefined control and
lazy branch selection, for every satisfying interpretation and shared
defined input tuple.

## Budget and sharing metric

`explore` retains the unchanged candidate and explores verified
successors to the requested number of rewrites per path. The depth
bounds the search. A step scans finitely many vertices, rules and
typed bindings. Visits to a node in a rank-recursive walk descend
strictly. The current traversal can revisit shared subgraphs, and
neither duplicate search states nor unfolded subterms are memoized.

`Contextual.cost` collects a finite set of vertex IDs reachable from
the ordered output boundary, then counts primitive and φ rows in
that set. Shared uses count once across all roots. Unselected arms
still count as syntactic reachability. `optimize_min` minimizes this
metric over the enumerated, replay-checked candidates. Storage
compaction, dynamic execution costs, and unbounded termination or
optimality remain separate obligations.

The [regression](../../tests/ssa/PeggyEgg.lean) has four ordered outputs.
The compression pattern matches none of the roots. One match has
two incoming uses from an add and another match sits in an undefined,
unselected φ arm. Rewriting the shared row keeps both operand addresses
equal. Depths zero, one and two give 10, 9 and 8 distinct reachable
application rows. The output observations for input 14 are
`[84, 84, bottom, bottom]`. A cyclic replacement is rejected. The
same outputs with one shared producer duplicated cost 11 instead of 10.

## Validation boundary

`CheckedProgram.verify` is an independent entry point for two
admitted tables and receipts for their corresponding outputs.
`Contextual.compareOutputs` uses the same check with reflexivity and
an empty rule table. It accepts different graph sharing or numbering
when corresponding unfolded outputs compare equal.
`compareOutputs_sound` then gives Figure 11 equality with no rule-law
assumptions. The regression checks the shared and duplicated graphs
and rejects swapped output slots.

The optimizer and validator expose the typed PEG observation boundary.
The checked SIMPLE pipeline composes this boundary with the loop-free
frontend and automatic scheduler for successful singleton returns.
[Pipeline contract and worked example](peggy-simple-validation.md)

## Checks

```sh
lake build --wfail +Silmaril.SSA.Peggy.Optimizer.Contextual.Thms PEGCoreTests PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker Silmaril.SSA.Peggy.Optimizer.Contextual.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
