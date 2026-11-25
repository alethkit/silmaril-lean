# Explicit φ view of λSSA block arguments

Import `Silmaril.SSA.PhiView.Thms`. A `Successor` is a path to a branch
leaf of an existing `LambdaSSA.Terminator`. An `EdgeOcc` pairs that path
with its source identity. Two arms of one case can name the same target
and still supply different operands.

Supply the source contexts after their block bodies and the discriminant
typing in `SourceTyping`. This gives each successor its scope, including
the binders along its case path. For each target, supply its ordered
parameter types. `BlockArgs` certifies that every existing branch argument
is a right-associated, unit-terminated tuple of variables. Each variable
has the slot's type in that successor's scope.

Use the certificates `args`, a selected occurrence `edge`, and the
environment `old` at its branch leaf to get the column, branch and payload.

```lean
let view := Silmaril.SSA.PhiView.ofBlockArgs args
(view.table.column edge, view.table.branch edge, Silmaril.SSA.PhiView.latch view edge old)
```

`Table.column` gathers the selected operands in parameter order.
`Table.branch` emits an ordinary λSSA branch and also accepts a freshly
constructed table. This lets a lowering supply its own mapping from Region
slots to occurrences. `branch_hasType` uses the target's packed type at its
label, and `branch_eq` recovers the original branch from a certified view.
The two conversion laws are equalities of the admitted presentations.

`latch_eq_transfer` is an iff for `Semantics.Region.Eval` of the selected
branch. Its only outcome is the same target, the tuple read from the old
environment, and unchanged state. For an internal target, the ordinary
`Region.Follow.step` binds this whole payload as the destination's single
parameter. Every retained occurrence has a typed operand in each row.
Execution reads only the selected column. The model uses total λSSA
environments and covers variable tuples.

The regression exercises both arms of a same-target case and a swap on
one backedge. The swap checks a single transfer. Loop execution, graph
scheduling, SoN readback, and undefined or poison values require further
semantics.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.PhiView.Thms +Silmaril.Proofs.SSA.PhiView.Regression'
```
