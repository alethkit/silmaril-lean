# Constructing a cyclic graph from two ordered quad blocks

`Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks` extends the initialized-bank
quad loop with a source preheader. The source has a preheader of ordered
assignments ending in a jump and a header of ordered assignments ending
in a conditional. True takes the sole syntactic backedge to that header.
False returns a typed register. The conditional and return read the
post-assignment bank.
[Initialized-bank loop](sea-of-nodes-quad-loop.md) ·
[Source definitions](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Blocks/Defs.lean)

The compiler translates the preheader from the initialized register bank.
Its computed outgoing versions provide the entry column. Before the
header is translated, `headerVersions` allocates one typed carried port
per register. The header can read these provisional definitions while
the feedback operand column is still pending. The ordered block compiler
then computes the header's outgoing versions and resolves that column
from them. Each column belongs to its own numbered producer context.
The result is the existing pure `Loop.Graph`.
[Loop graph](../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean)

`Program.latch_agrees` and `Program.latch_slot` prove simultaneous whole-bank
and per-slot agreement for either incoming occurrence. The entry uses
one preheader snapshot. The backedge uses one snapshot of the old header
bank and its producer results. `Program.lower_step` agrees on the test,
return, and feedback values. `Program.lower_evalBackedges` gives exact
return or budget exhaustion for every input and backedge budget. A zero
budget still permits a return from the first header activation.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Blocks/Thms.lean)

The fixture starts at `(x, y) = (99, 5)`, then the preheader sends
`(7, 5)`. The first backedge latches `(5, 12)` and the next activation
uses those values to produce `(12, 17)`. The source and graph both return
`29` with two backedges. With a budget of one they both return `none`.
With a counter of one they return `12` at budget zero. The stride is
forwarded through the carried port.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Blocks/Regression.lean)

This slice follows Cliff Click's *From Quads to Graphs: An Intermediate
Representation’s Journey*, Rice technical report CRPC-TR93366-S,
October 18, 1993, §3.1 on provisional loop-head definitions and §4.1
on matching operands to control occurrences. It allocates the full
bank. Minimal Φ placement, additional backedges, and interior control
are outside the admitted profile. The archived PDF has SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Thms
```
