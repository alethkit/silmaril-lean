# Straight-line quads and use-def edges

`Silmaril.SSA.SeaOfNodes.Quads.Defs` models one ordered basic block with a
fixed, fully initialized bank of typed mutable registers. An assignment
has an opcode, an ordered tuple of source registers, and one destination.
The executable `Code.eval` reads every operand from the old bank,
applies a total pure opcode, then writes the destination. The sole
observation is the value read by the return instruction.

`Code.lower` emits an existing numbered RVSDG graph, using the pure
opcodes and model from the [diamond development](../../../../Silmaril/SSA/SeaOfNodes/Diamond/Defs.lean).
The current-definition table starts with entry ports. At each assignment
the compiler emits operand edges from the old table, then records the new
producer's output for the destination. `rebind_same` and `rebind_other`
specify those updates. `Code.lower_run` proves exact agreement of the
returned value for every typed initial bank and total model.
[Theorem header](../../../../Silmaril/SSA/SeaOfNodes/Quads/Thms.lean)

The regression checks the producer indices for `x := x + y` after an
intervening write to `y`, and for the later use of the new `x`. The source
and graph evaluators both return 34 from the initial bank `(3, 5)`.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Regression.lean)

This slice covers the ordered instruction semantics and local use-def
lookup of §§2–3.1. Admission is intrinsic in the register and opcode
types. The profile has one return, no control joins or backedges, and no
partial or effectful opcodes. A bridge from the Machine λRTL or LambdaSSA
block APIs to this register bank, and SSA construction over multiple
predecessors, remain separate.

Cliff Click, *From Quads to Graphs: An Intermediate Representation’s
Journey*, Rice technical report CRPC-TR93366-S, manuscript dated October
18, 1993, §§1–3, especially Figures 2, 5 and 6. The archived PDF has
SHA-256 `8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf) ·
[Coverage map](../coverage.md#from-quads-to-graphs)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Regression
make check CHECK_TARGETS=+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Regression
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Thms
```
