# Pruning dead carried fields in a two-block quad loop

`Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune` derives a carried-field
mask from the source program's compiled reaching wires. It feeds the
header's numbered operand rows and the conditional and return roots
to the shared RVSDG backward liveness sweep. An argument address in
the carried segment identifies a register value read from the old bank.
A read after a local assignment names that assignment's producer.
[Source loop](sea-of-nodes-quad-preheader-loop.md) ·
[Shared liveness sweep](../../Silmaril/SSA/RVSDG/NestedTheta/Liveness/Defs.lean)

`pruneWith` validates the mask against all header operands, the test,
the return, and the retained feedback column. It returns a typed
`Loop.Graph` whose carried signature contains just the retained fields,
in source order. The preheader projects its outgoing column into that
signature. The header reindexes carried argument references and leaves
producer numbers and fixed inputs intact. A failed reference check or
a mask with no reduction yields `none`.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Blocks/Prune/Defs.lean)

`initial_agrees` and `feedback_agrees` prove that both latches give the
projection of the corresponding source bank. `step_agrees` preserves the
branch decision and returned value and relates continuation banks by
projection. `eval_agrees` covers every backedge budget, including
exhaustion, and `returns_iff` characterizes all finite returns.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Blocks/Prune/Thms.lean)

On the shared quad example, the pass keeps the counter, `x`, and `y`,
reducing the bank from six fields to three. The header produces fresh
scratch and predicate values before reading them. The stride is read only
in the preheader. A proposed mask that drops `y` is rejected. The shrunk
graph returns `29` at budget two, exhausts budgets zero and one for the
same input, and still gives the zero-backedge return of `12` on the
counter-one input.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Blocks/Prune/Regression.lean)

This is a conservative filter of the full-bank Φ construction from the
two-block source profile. It keeps every producer, so an input used only
by a dead producer can keep its carried field. The source construction
follows the predecessor and loop-header treatment in Cliff Click's
*From Quads to Graphs*, §3.1 and §4.1, Rice TR CRPC-TR93366-S,
October 18, 1993.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Thms
```
