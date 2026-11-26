# Trivial φ elimination for the pure Sea of Nodes diamond

In *From Quads to Graphs* §4.1 and Figure 9, each Select pairs a data
input with its incoming control edge. Compose forwards the value
produced by the selected predecessor. If both predecessors supply the
same typed wire, either selection returns that wire.
[Archived report CRPC-TR93366-S, printed p. 9](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf#page=10)

`Silmaril.SSA.SeaOfNodes.Diamond.PhiElim.eliminate` decides equality
using the existing `Origin.address`. Argument positions and
producer/port positions are distinguished, and the two wires share a
typed scope. Success returns a `Pure.Program` with the original producer
table and the first slot's result wire. `eliminate_eq_some_iff` and
`eliminate_eq_none_iff` give the exact acceptance and output contract.

`denote_eq` and `returns_iff` agree on every input in any total pure
primitive model of the diamond profile. `lower_run_eq` compares the
existing numbered RVSDG γ with the straight-line lowering under their
induced models. Both return the same singleton tuple. The proof uses the
shared table of producers available before either arm. Effectful,
trapping or control-dependent producers require a different profile.

The fixtures check both Region predecessor orders and both selector
values. Reversing the slots of two distinct producer addresses still
rejects the rewrite, even when both producers compute the same value.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.PhiElim.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.PhiElim.Regression'
```
