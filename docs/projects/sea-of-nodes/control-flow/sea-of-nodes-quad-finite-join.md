# Finite quad joins and acyclic composition

`Silmaril.SSA.SeaOfNodes.Quads.Join.Finite` builds on
[the binary quad join](sea-of-nodes-quad-join.md). An incoming table is
a finite list of closed ordered quad blocks over one typed register bank.
A `Fin` index identifies an occurrence by position, so two occurrences can
name identical blocks and still have distinct indices. `Table.incoming`
constructs each column from that block's final reaching-version map.
Assigned registers name their last local producer, and untouched registers
name their input ports. Each column is in its own predecessor's scope.

`Table.arm_results` identifies the actual numbered child result wires
with that occurrence's incoming column. `Table.arm_run` recovers its
entire final source bank. An empty table has no selectable index. A
singleton table can use its compiled block directly. A stage uses the
native RVSDG γ for two or more occurrences. A typed predicate decision
tree returns an in-range occurrence index and passes the current bank
to the selected child. Only that child executes.
[Definitions](../../../../Silmaril/SSA/SeaOfNodes/Quads/Join/Finite/Defs.lean) ·
[Theorems](../../../../Silmaril/SSA/SeaOfNodes/Quads/Join/Finite/Thms.lean)

A plan sequences these stages. Lowering binds each selected bank to a
γ result tuple and uses its output ports for the next stage.
`Plan.lowerFrom_eval` proves agreement starting from an arbitrary typed
reaching-version map. `Plan.lower_run` gives exact agreement of the entire
returned bank. `Plan.lower_append_run` states that compiling an appended
plan agrees with running the compiled graphs in sequence.

The fixture checks three separate incoming occurrences and the origin
columns of their actual numbered children. One arm changes the predicate
used by a second join, so the second selector must read the first join's
result. Starting from `(x, y) = (3, 5)`, the three choices return
`(8, 13)`, `(3, 8)` and `(13, 18)`, respectively.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Join/Finite/Regression.lean)

This slice realizes the closed, occurrence-indexed part of Cliff Click,
*From Quads to Graphs: An Intermediate Representation’s Journey*, Rice
technical report CRPC-TR93366-S, manuscript dated October 18, 1993,
§3.1 and §4.1, especially Figures 6 and 9. The profile is structured
acyclic sequences of joins with closed predecessors and total quad
operations. It carries the full bank and leaves dominator-frontier or
pruned Phi placement, shared arbitrary CFG blocks, and cyclic construction
outside this result. The archived PDF has SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Join.Finite.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Join.Finite.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Join.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
```
