# Three-block tail-tested quad loops

`Quads.Loop.Tail.Source` is a typed table of three ordered quad blocks.
The checker admits entry → header → latch at indices zero, one, and
two, with the latch branching
back to the header on true and returning a register on false. The
source runner follows the original terminators and charges one unit
per block visit. `Source.check_sound` proves that a successful check
preserves all bodies and terminators.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Defs.lean) ·
[Theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Thms.lean)

The profile uses the ordered CFG blocks of Cliff Click's *From Quads
to Graphs*, §2 and Figure 1, and the current-definition map and
provisional loop-head inputs of §3.1 and Figure 6. The two header
columns associate data with the actual entry and feedback occurrences,
as in §4.1 and Figure 9. The target uses the Region and explicit
control edges described in §6 and Figure 15. The pinned source is Rice TR CRPC-TR93366-S,
October 18, 1993, SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

The compiler allocates the full typed bank of provisional header
ports before compiling the header quads. The latch starts with the
header jump's outgoing versions, so it can read both header-local and
carried values. `Program.feedback_column` proves that the native
backedge picks exactly the latch's final versions. Entry has its own
column and producer scope, and `Program.latch_agrees` covers simultaneous
latching for either occurrence. In the native `Loop.Graph`, one
activation schedules the header and latch in order across the forced
jump. The distinct latch boundary is present in the source CFG.
The checked shape and pure total operations make this fusion sufficient
for return observations.
[Native graph](../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean) ·
[Reused compiler](sea-of-nodes-quad-preheader-loop.md)

At source fuel below three, no return is possible. At fuel `f ≥ 3`,
`Source.lower_run` proves exact agreement with native backedge budget
`(f - 3) / 2`, including exhaustion. A run that returns after `b`
backedges needs one entry visit and `b + 1` header/latch pairs, for
`2 * b + 3` source visits. `Source.returns_iff` gives finite return
agreement in both directions.

The regression forwards `y = 5` on entry, takes `y = 12` from the
latch's assignment on the first feedback, and reads that value in the
next header. The two-backedge input returns `29` at source fuel seven
and exhausts at six. The checker rejects an entry-to-latch bypass that
would give the latch two incoming edges. Extra joins, multiple
backedges, and Φ pruning are outside this profile.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Thms
```
