# Checked quad chains in tail-tested loops

`Quads.Loop.Tail.Chain.check` starts from the supplied entry block ID and
follows the source's actual jump targets. It accepts a preheader jump, a
nonempty chain of activation blocks, and a final test whose true arm jumps
to the discovered header and whose false arm returns. The checked path
stores the original IDs and proofs of the source terminators. It requires
every block in the table to appear once in the entry and activation order.
The one-block activation has a header that is also the latch.
[Checker and lowering](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Chain/Defs.lean) ·
[Three-block profile](sea-of-nodes-quad-tail-loop.md)

The ordered blocks follow Cliff Click's *From Quads to Graphs*, §2 and
Figure 1. The full-bank provisional loop-head definitions and the
cross-block current-definition map use §3.1 and Figure 6. The separate
entry and feedback columns follow §4.1 and Figure 9, and the native loop
Region and test follow §6 and Figure 15. The source pin is Rice TR
CRPC-TR93366-S, October 18, 1993, SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

`Path.outgoing_eq` proves that compiling the fused activation gives the
same typed reaching versions as compiling each block and passing its
outgoing map across the original jump. The latch's final map resolves
the native feedback column in the pending header argument order. Entry
and feedback point to different source predecessors even when the header
doubles as latch. Pure producers run in source order in one native
`Loop.Graph` activation.
[Proof interface](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Chain/Thms.lean) ·
[Native loop](../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean)

For an activation of `L` blocks and native backedge budget `b`,
`Program.lower_budget` proves agreement at source fuel `1 + L * (b + 1)`
and for any surplus smaller than `L`. At fuel `f` below `1 + L`
the source exhausts. At or above that cutoff, `Program.lower_run` gives
native budget `(f - (L + 1)) / L`. The finite-return equivalence follows
in both directions for the original source table.

The four-block fixture keeps original IDs in order `[2, 0, 3, 1]`.
The internal block writes `y = 7`, the latch reads it and writes
`y = 14`, and the next header reads that feedback value. The source
returns `37` at fuel ten and exhausts at nine. The checker rejects an
internal cycle, a jump on the exit arm, and feedback to the wrong block.
One- and two-block activations also exercise the earlier two- and
three-block profiles. The admitted scope is one pure chain with one
tested backedge and a full carried bank.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Chain/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Thms
```
