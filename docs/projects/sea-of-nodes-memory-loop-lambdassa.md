# Tail-tested Sea of Nodes memory loop to λSSA

`Memory.Loop.LambdaSSA.lower` emits a `LambdaSSA.Region.cfg` with a preheader
and one loop header. The header emits the ordered loads and stores and
compares the compiled Return operand to the invariant stop argument.
The comparison preserves the heap. A match exits with the packed word
and the heap after the body. Otherwise the header's false successor takes
the backedge with that same heap. [Source loop](https://github.com/hiloopai/silmaril-lean/pull/3318) ·
[Heap instruction semantics](https://github.com/hiloopai/silmaril-lean/pull/3363)

The preheader and backedge are separate PhiView occurrences. Both carry
unit as their scalar argument. The only changing loop-carried value is
the entire heap, threaded as the ambient state of `Region.Eval` and
`Region.Follow`. `edge_transfer_iff` identifies both transfers, and
`activation_eval_iff` checks the ordered effects and the tail test of one
header execution. [Pure-loop CFG pattern](https://github.com/hiloopai/silmaril-lean/pull/3279) ·
[PhiView](https://github.com/hiloopai/silmaril-lean/pull/3186)

`lower_hasType` checks the emitted CFG. `returnsFrom_iff` starts the counted
target execution from the source arrival's latched heap, and
`returnsAfter_iff` specializes to entry with exactly the same number of
backedges. `follow_iff` relates the counted executions to the ordinary
target continuation. `returns_iff` preserves and reflects the word and
whole final heap of every finite return.

The regression reuses the source loop fixture. An immediate exit still
copies the tail cell and clears it. The repeated case takes two backedges.
Its second activation reads the value written by the first activation
and forwards its own updated heap. The checks reject a one-backedge
return. The profile is one tail-tested loop over initialized 64-bit
word cells, with invariant scalar inputs.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Regression'
```
