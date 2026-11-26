# A cyclic quad loop with typed header arguments

`Silmaril.SSA.SeaOfNodes.Quads.Loop` constructs a single loop from the
[ordered quad source](sea-of-nodes-quads.md) and a fully initialized typed
register bank. A closed straight-line activation reads operands before
overwriting their destinations. Its terminator reads a Boolean register
from the updated bank. True takes the sole backedge, carrying that bank.
False exits with the specified register from the same bank. Zero backedges
means the first activation runs and exits.

`headerVersions` allocates a typed header argument for each register before
translating the activation. These arguments stand for the pending definitions
at the header. They can be used by the body before the backedge is available.
The compiler emits the existing pure producers and computes the outgoing
register map in the same traversal. The entry column names the initial input
ports. The backedge column names the independently computed outgoing origins,
including the current header argument for any register left untouched.
`Program.lower` supplies those two columns to the existing
[Loop.Graph](../../../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean), which latches the
selected column as one tuple. The fixed input segment of the graph's header
interface is in scope, and the translated activation reads the carried segment.

`compile_agrees` proves that the outgoing wires recover the whole mutable
register bank for arbitrary typed inputs and total opcode models.
`Program.lower_step` gives equality on the returned value or the full
backedge bank. `Program.lower_returnsAfter_iff` preserves and reflects finite
returns with the exact backedge count. The bounded evaluators also agree at
every budget. [Definitions](../../../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Defs.lean) ·
[Theorems](../../../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Thms.lean)

The regression accumulates an untouched stride while decrementing a counter.
It checks the producer inputs for both self-reads, the separate entry and
backedge origins, and forwarding of the latched stride even when the
original entry bank differs. Starting with total 10 and stride 7, count
1 exits at 17 with zero backedges, and count 3 exits at 31 with two.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Regression.lean)

This is the single-header, single-backedge instance of Cliff Click,
*From Quads to Graphs: An Intermediate Representation’s Journey*, Rice
technical report CRPC-TR93366-S, manuscript dated October 18, 1993, §3.1
and Figure 6. It allocates header arguments for the full bank and closes
the two columns by construction. The profile covers tail-tested loops
with total pure operations. Pruned Phi placement and general CFG
construction remain separate. The archived PDF has SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Loop.Thms
```
