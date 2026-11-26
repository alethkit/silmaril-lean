# A checked quad loop with an internal diamond

`Quads.Loop.Tail.Diamond.check` reads the original typed quad source
table. It checks six distinct blocks: a preheader jump, a header test,
two arms jumping to the same merge, a merge jump, and a latch test.
The latch's true occurrence returns to the header. Its false occurrence
returns a typed register. The checker keeps the source block IDs and
proofs of each terminator. The two merge columns are ordered true,
then false, independent of the numeric block IDs.
[Checker and lowering](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Defs.lean)

The source follows Cliff Click's *From Quads to Graphs*, §2 and
Figure 1 for ordered CFG blocks, §3.1 and Figure 6 for current
definitions and pending loop-head inputs, §4.1 and Figure 9 for
associating data with the chosen predecessor, and §6 and Figure 15
for the Region and If graph representation. The pinned manuscript
is Rice TR CRPC-TR93366-S, October 18, 1993, SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

The existing quad join compiler emits each arm into its own numbered
γ child. The child's results are calculated from that arm's local
reaching versions. The selected γ result supplies the complete typed
bank of merge arguments to the shared merge quads and then the latch.
A preheader prefix initializes the θ binder. A continuing latch passes
the whole updated bank back to that binder in one operation. A stopping
latch exposes the result register from the same updated bank.
The target is existing numbered `RVSDG.NestedTheta.Graph`, with γ inside θ.
[Quad join compiler](../../Silmaril/SSA/SeaOfNodes/Quads/Join/Finite/Thms.lean) ·
[Native graph](../../Silmaril/SSA/RVSDG/NestedTheta/Defs.lean)

`Program.selected_predecessor` identifies the source ID selected by the
γ tag. `Program.merge_run` proves that the selected occurrence supplies
the entire bank. `Program.activation_run` gives the latch's exact
continuation tag and bank. `Program.lower_run` relates `k` units of
native θ fuel to `1 + 4 * k` source block visits and any surplus smaller
than four. `Program.returns_iff` relates every finite native return to a
successful run of the original source table in both directions.
[Proof interface](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Thms.lean)

The regression enters at block 4, runs true arm 5, feeds back through
latch 1, and then runs false arm 0. The arms supply different numbered
definitions of `y`. The first merged value gives `x = 7` in the
feedback bank. The false arm reads that bank and the next merge gives
`x = 14`. Nine source visits or two θ activations return `14`.
Eight visits or one θ activation exhaust. A counter-one input returns
`12` through the false arm without feedback. The checker rejects
different arm merge targets and a wrong feedback target.
This is one pure diamond, one tail test, and a full carried bank.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Join.Finite.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
```
