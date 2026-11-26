# A closed quad branch and join

`Silmaril.SSA.SeaOfNodes.Quads.Join` extends the
[straight-line quad slice](sea-of-nodes-quads.md). An input predicate
chooses one of two closed predecessor blocks. Each block executes ordered
assignments over the same fully initialized typed register bank. The join
executes against the bank delivered by the selected edge and returns a
single value.

The lowering starts a fresh version map in each predecessor. Its outgoing
column lists the last definition of every register in bank order. An
untouched register still names its input port. Both columns have the same
typed interface, with a separate producer numbering for each predecessor.
`Program.arm_results` identifies the columns in the numbered children.
`predecessor_selected` relates the selected Region slot to its If projection.
The numbered γ executes only that child, and its output ports are the
join's block arguments. `Program.arm_run` proves the per-edge bank
agreement, and `Program.lower_run` proves exact returned-value agreement
for all typed inputs and total pure opcode models.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Quads/Join/Defs.lean) ·
[Theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Join/Thms.lean)

The [existing Sea of Nodes diamond](../../Silmaril/SSA/SeaOfNodes/Diamond/Defs.lean)
has one producer table before the If and a single Phi whose operands are both scoped to
that table and its inputs. Its γ children only return a captured value.
Branch-local production followed by a join body requires a child region
with its own producer table and a multi-port exit. This slice uses the
existing numbered RVSDG γ with fresh local scopes and one simultaneously
selected argument tuple. It passes the whole bank, including
unchanged registers.

The regression writes `x := x + y` twice on the true predecessor and writes
only `y` on the false predecessor. It checks the exact origins of the
self-read and the outgoing values, then checks the join result for both
inputs and both predecessor orders. On entry `(x, y) = (3, 5)`, the join
returns 18 on true and 11 on false.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Join/Regression.lean)

This covers the closed-predecessor portion of Cliff Click, *From Quads to
Graphs: An Intermediate Representation’s Journey*, Rice technical report
CRPC-TR93366-S, manuscript dated October 18, 1993, §§3–6, especially
§3.1, §4.1 and Figure 9, and the Region and If of §6. The encoding models
the selected incoming values with typed arguments. Open predecessors,
loop Phi repair, register liveness and general SSA construction remain
outside this profile. The archived PDF has SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf) ·
[Coverage map](sea-of-nodes.md#from-quads-to-graphs)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Join.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Join.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
```
