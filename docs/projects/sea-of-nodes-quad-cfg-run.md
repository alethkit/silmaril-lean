# Executable terminators for acyclic quads

`Silmaril.SSA.SeaOfNodes.Quads.CFG.Run` adds source execution to the
topologically ordered quad graph. Cliff Click's *From Quads to Graphs:
An Intermediate Representation’s Journey* models sequential quads and
their control transfer in §2, definition maps in §3.1 and Figure 6, and
the correspondence of data inputs with control occurrences in §4.1
and Figure 9. The source is Rice TR CRPC-TR93366-S, October 18, 1993.
The archived PDF has SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

A terminator jumps, tests a typed predicate, or returns a typed slot.
The test and return read the bank after the block's ordered quads.
Each edge carries its successor and exact incoming position. Its type
checks that the listed predecessor is its source. A program's coverage
proof accounts for every incoming occurrence, and conditional arms
reference distinct edges. The runner needs only the initial bank.
Block numbers strictly increase on each transfer, so it always reaches
a return on the admitted finite profile.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Quads/CFG/Run/Defs.lean)

`Program.run_iff` proves that the runner returns exactly the guard-selected
checked path and the value read by its final terminator. `Edge.take_eval`
identifies the successor bank transfer, and `Edge.take_occurrences` identifies
the appended successor and incoming position. `Program.terminator_from_versions`
proves that reading the post-body version map gives the same terminator
observation, including the exact edge on a transfer.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Quads/CFG/Run/Thms.lean) ·
[Reaching versions and placement](sea-of-nodes-quad-cfg-phi.md)

For a λSSA emitter, `CFG.compileBlock` provides each block's numbered producer
body and outgoing wires. The existing `Diamond.LambdaSSA.schedule` can emit
the body. Those wires supply the tested predicate, returned slot, and branch
arguments. A `PhiView.EdgeOcc` pairs the source block number with the jump
leaf or the true/false case leaf. The emitter must associate that leaf with
the source `Edge.target` and `Edge.slot`, then prove its arguments feed the
corresponding incoming column. The ordinary λSSA execution observation
contains the target label and payload, so equal-label, equal-payload arms
need a leaf-level correspondence or distinct forwarding labels to recover
the occurrence. Sibling blocks cannot capture each other's local binders.
A first target lowering can pass the full bank as typed block arguments.
Using only placed Φs would also require a representation for inherited
cross-block values. This slice ends at the source runner and version
interface, with target emission and return correspondence left open.
[Scheduler](../../Silmaril/SSA/SeaOfNodes/Diamond/LambdaSSA/Thms.lean) ·
[Occurrence-indexed arguments](../../Silmaril/SSA/PhiView/Defs.lean)

The executable fixture tests a predicate overwritten before its branch,
a bypass, an unconditional jump, and two parallel arms to the same
successor. The parallel cases both return `11` and record distinct incoming
positions `1` and `2`. The bypass and the path through the updating arm
return `13` and `21`.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/CFG/Run/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.Run.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.Run.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.CFG.Run.Thms
```
