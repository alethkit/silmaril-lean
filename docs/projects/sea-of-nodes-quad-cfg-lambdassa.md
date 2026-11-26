# Typed λSSA emission for acyclic quads

`Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA` emits one ordinary λSSA CFG
for the checked topological quad profile. Its source uses the ordered
blocks of Cliff Click's *From Quads to Graphs: An Intermediate
Representation’s Journey* §2, reaching definitions in §3.1 and Figure 6,
and the association of data inputs with control occurrences in §4.1 and
Figure 9. The source is Rice TR CRPC-TR93366-S, October 18, 1993.
The archived PDF has SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

For each register slot and source edge, `boundOperand` pairs the typed
outgoing producer wire with the reaching version and the definition bound
at the destination. The incoming name comes from that predecessor's
computed column. The header binds either the common inherited version or
the Φ placed at that destination by the source plan. A λSSA block receives
one typed packed register bank, so inherited fields remain available
across sibling block scopes. The emitter preserves the full bank and
includes no liveness-based pruning.
[Reaching-version plan](sea-of-nodes-quad-cfg-phi.md) ·
[Source runner](sea-of-nodes-quad-cfg-run.md)

The existing scheduler emits the quad producers as lets. The generated
jump, case, or return reads the final layout after those lets. Each
`PhiView.EdgeOcc` addresses an actual generated branch leaf. The left and
right leaves stay distinct even when they share a successor label.
`selected_packet` identifies the source edge, target label, and the bank
latched from that edge's computed header. Ordinary λSSA observations erase
the leaf position. Occurrence preservation is stated on the generated
leaves and operands.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Quads/CFG/LambdaSSA/Defs.lean)

`lower_hasType` checks the emitted region with one bank parameter per
local block and one typed external return. `lower_eval_iff` characterizes
all finite observations in the existing λSSA operational semantics as
external exit zero, the source runner's packed return, and unchanged
ambient state. `returns_iff` states the correspondence on the typed
source result. The proof uses the source topological bound and covers
the checked acyclic profile.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Quads/CFG/LambdaSSA/Thms.lean)

The regression checks that the conditional tests the overwritten predicate
at the newest let. A bypass and an updating predecessor feed a Φ for
`x`, and a later case uses two distinct occurrences of the same target.
Both alternatives have λSSA return derivations. Their returned values
are `4` and `3`.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/CFG/LambdaSSA/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.LambdaSSA.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.LambdaSSA.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.Run.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA.Thms
```
