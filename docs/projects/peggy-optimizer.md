# Bounded root optimization for loop-free PEGs

The [executable optimizer](../../Silmaril/SSA/Peggy/Optimizer/Defs.lean)
discovers rule instances, generates PEG rows, replays sorted Egg
explanations, and chooses a candidate. It uses a single result, a fixed
typed parameter list, and a ranked zero-loop graph with parameters,
strict partial primitives and lazy φ. This is a bounded root search
drawing on the saturation and selection stages of §4 and §8. The
[contextual optimizer](peggy-contextual-optimizer.md) extends discovery
and replay to shared internal nodes and ordered outputs. The
[PEG project notes](peggy.md) identify the paper and its artifact hash.

## Matching and generation

A client supplies sorted rule schemas and an opcode comparison. The
left pattern can be any finite sorted Egg term. The right pattern is
one primitive or φ application whose operands are typed variables.
Each variable is assigned an existing vertex of its declared sort.
Repeated occurrences share one binding. The matcher enumerates the
finite product of those typed choices and checks that the instantiated
left pattern exactly equals the unfolded current root using Egg's
sorted term comparison. Matching uses the current graph, including
rows generated on earlier steps. It performs syntactic matching and
can revisit equivalent unfolded trees at different vertices.

[`RootMatch.sound`](../../Silmaril/SSA/Peggy/Optimizer/Thms.lean)
connects a discovered binding to instantiation of its rule law.
The guard premises are the equalities of the actual instantiated
guard sides. The law quantifies over all partial Egg variable
valuations, including bottom.

The generator creates one fresh row at vertex zero with the instantiated
operands. It shifts all old vertices and references by `Fin.succ`
and makes the new row the root. A computed rank admits that graph
through the existing executable rank checker, and `extend_admitted`
proves that this rank always succeeds.
[`Extension.fold_succ` and `Extension.denote_succ`](../../Silmaril/SSA/Peggy/Optimizer/Extension/Thms.lean)
prove that the injection preserves every old node's fold and its
native Figure 11 partial value at the shared inputs.

The producer proposes an ordinary Egg rewrite receipt and reflexivity
for each instantiated guard. The existing replay checker compares both
guard endpoints and the actual source and generated root terms.
Consequently the executable guard mechanism covers pairs with identical
unfolded syntax. Guards that need independent equalities are outside
this matcher. Every candidate that enters the search carries the
replayed root certificate.

## Search, cost and observation

`explore` enumerates checked forward root rewrites to the supplied
path depth, with the unchanged program as an option at every visit.
The procedure composes the step certificates and explores every
accepted successor it generates within that depth. Each path retains
its own PEG candidates and certificates. The
[fixed-table E-PEG closure](peggy-saturation.md) remains available for
its different input profile.

`Program.cost` counts applications in the unfolded result tree.
Parameters cost zero. Repeated uses and unselected arms count in
this static metric. Old rows are retained, including rows that become
unreachable. By `optimize_mem` and `optimize_min`, the chosen
candidate belongs to the enumerated list and minimizes that metric
over the list. A tie keeps the earlier candidate.
`Candidate.sound` gives equality of the native Figure 11 observation
on the same defined inputs for every interpretation satisfying the
supplied Egg rule table. These interpretations still evaluate
partial primitives and φ as in the existing bridge.

The budget bounds the depth of each path. A step checks a product of
vertex choices across rule variables, and unfolding can duplicate
shared subgraphs. Search size can grow exponentially in the depth.
Unbounded termination, RHS trees and variable
roots, class-based matching, proof search for nonreflexive guards,
dead-row elimination, CFG reversion and optimality for execution cost
remain separate obligations.

## Worked regression

The [fixture](../../tests/ssa/PeggyEgg.lean) starts with
`φ(yes(), (x+x)+x, bottom())`. It discovers the guarded branch
rewrite and creates a new add root, then matches that generated root
against a repeated-variable rule and creates a triple root. Depths
zero, one and two yield application counts five, two and one. The
chosen graph retains the original six rows and adds two. The same
fixture checks guard rejection for false and undefined control,
rejection of the repeated-variable rule when the last operand is
different, evaluation to 42 at input 14, and exact native observation
equality for all defined inputs in the example dialect.

```sh
lake build --wfail +Silmaril.SSA.Peggy.Optimizer.Thms PEGCoreTests PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker Silmaril.SSA.Peggy.Optimizer.Extension.Thms
lake env leanchecker Silmaril.SSA.Peggy.Optimizer.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
