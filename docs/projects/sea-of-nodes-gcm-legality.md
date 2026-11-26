# Checked placement for one Sea of Nodes floating node

`Silmaril.SSA.SeaOfNodes.GCM.checkPlacement` checks a proposed insertion
for a single pure total computation. The typed CFG supplies the block
arguments, bindings and terminators. Its structural paths include both
arms of every conditional. The checker applies the operand constraint
from Click’s schedule-early pass and the use constraint from
schedule-late to a supplied candidate. [Definitions](../../Silmaril/SSA/SeaOfNodes/GCM/Defs.lean) ·
[Typed CF definitions](../../Silmaril/SSA/MLIR/CF/Basic/Defs.lean)

## Certificate and positions

A supplied `DominatorTree` assigns each block a distinct tree address with
the empty address at entry. It proves that every admitted block is
reachable and that address-prefix ancestry implies dominance along all
structural entry paths. A certificate can omit dominance facts or leave
blocks unadmitted, so rejection is conservative. This keeps the CFG and
certificate in SSA. The existing Machine and Automata dominator-tree APIs
sit outside SSA’s allowed region dependencies. [Region map](../../regions.toml)

A position counts the original bindings completed in a block. Position
zero is after block-argument binding. At any position, the proposed
insertion runs after its already available operands and before the
original instruction or terminator reads. The checker verifies that
the position is in bounds. Same-block constraints compare these positions.

An ordinary use gives a position directly. A Phi use names its source
block, a branch occurrence and the argument index. The occurrences are
an unconditional jump and the two separate conditional arms. The argument
index must be in range for the chosen target’s typed parameter list. Its
read takes place at the source terminator after all the source bindings.
[Theorems](../../Silmaril/SSA/SeaOfNodes/GCM/Thms.lean)

## What acceptance proves

- `Use.phi_point?_eq_some_iff` characterizes successful Phi resolution.
  The source terminator has the named outgoing occurrence with the
  requested argument, and the resulting position is its source block’s
  final cut.
- `checkPlacement_sound` proves `Legal` for each accepted placement.
  The candidate and all supplied operand and resolved use positions are
  reachable and in bounds. Every entry path to the candidate visits each
  operand’s block, and every entry path to a resolved use visits the
  candidate’s block. When two positions share a block, the supplying
  position is at or before the receiving position under the cut convention.

The request supplies the operand availability sites and the uses of one
pure total node. The theorem assumes those are the relevant sites and
checks position legality. Deriving the full def-use relation and
implementing the insertion belong to a graph-to-CFG bridge. That bridge
must also supply any cross-block values through CF block arguments.
Tree construction (§2.1), discovery of candidate bounds (§§2.2–2.3), and the
loop-depth heuristic (§2.4) remain open. Reordering pinned, faulting or
effectful operations, preserving values, and proving execution
equivalence require their own models and proofs.

## Branch regression

In the regression, entry branches to a left or right arm and both arms
pass an argument to the merge. The checker accepts a placement at the
end of the left arm for its incoming Phi operand. Passing an ordinary
use at the merge would accept a placement there. The actual Phi use
rejects that candidate, and a path to the left arm witnesses why the
merge cannot dominate the read. The regression also checks an absent
branch occurrence, an out-of-range edge argument, a placement before
its same-block operand and a placement after its same-block user.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.Regression'
```

## Source

Cliff Click, *Global Code Motion/Global Value Numbering*, PLDI ’95,
pp. 246–257, §§2.1–2.4. The archived UW PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
[Proceedings](https://doi.org/10.1145/207110.207154) ·
[Archived PDF](https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf) ·
[Source-to-Lean inventory](sea-of-nodes.md)
