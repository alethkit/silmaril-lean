# Sea of Nodes memory diamond to λSSA

`Memory.Diamond.LambdaSSA.lower` lowers the occurrence-indexed memory
diamond to an ordinary `LambdaSSA.Region.cfg`. Its entry case takes the
evaluated guard. Each arm emits one λSSA let per memory operation in
source order, then branches to the same join. Only the selected block
runs. The join consumes its exported word and runs the common suffix.
[Source memory diamond](https://github.com/hiloopai/silmaril-lean/pull/3280) ·
[Arm-local CFG shape](https://github.com/hiloopai/silmaril-lean/pull/3311)

`Instruction` gives typed load and store opcodes the existing
`Heap.read` and `Heap.write` behavior. The whole heap is the ambient state of
`Region.Eval`. The incoming branch carries the word as a packed scalar
argument and `Region.Follow` carries the resulting heap into the join.
`edge g slot` recovers the actual arm jump in that predecessor order.
`edge_transfer_iff` makes the two observations explicit at the branch
boundary. The scalar is read from the old environment through PhiView,
and the heap at the end of the arm becomes the suffix's initial heap.
[PhiView](https://github.com/hiloopai/silmaril-lean/pull/3186)

`lower_hasType` checks the CFG. `returns_iff` preserves and reflects the
source word and the entire final heap. `lower_eval_iff` also identifies
the exact external label and packed payload of every finite target run.
The profile has one diamond with ordered loads and stores over total
access to initialized 64-bit word cells.

The regression checks both outcomes in both predecessor orders. Each
arm saves an old value in a different cell, overwrites a common cell,
and exports a different word. The suffix stores the selected export
and returns a load of the common cell. The checks include exact heaps
and reject a heap containing a write by the untaken arm.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Regression'
```
