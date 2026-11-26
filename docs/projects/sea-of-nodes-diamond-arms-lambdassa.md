# Sea of Nodes diamond with arm-local producers

The original pure diamond shares a producer table and returns a single Phi. In
`Silmaril.SSA.SeaOfNodes.Diamond.Arms.Defs`, `Graph.shared` supplies the
predicate and the prefix visible to both arms. Each `Arm` extends that prefix
with its own `Dataflow` and supplies typed wires for a common result vector.
`Graph.Returns` follows the taken projection to its predecessor slot and
evaluates only that arm with the native `Dataflow.eval`. This is the
Region/Phi input correspondence in Click and Paleczny, §§2.1–2.4 and §3.1.
[Original pure diamond](https://github.com/hiloopai/silmaril-lean/pull/3135) · [IR ’95 proceedings](https://doi.org/10.1145/202530.202534)

`Diamond.Arms.LambdaSSA.Thms` exposes `lower` and `lower_hasType`. The
scheduler binds the shared producers before entering an ordinary
`LambdaSSA.Region.cfg`. Its case dispatches to the true or false label with a
unit argument. Each arm schedules its own producers before transferring a
packed result tuple to the join. The join forwards that tuple to external
exit zero. `edge g slot` selects the arm's jump occurrence.
`edge_branch` recovers its ordinary branch, and `edge_latch` identifies its
packed tuple with the source wires read from that arm's final environment.
`edge_transfer_iff` connects this simultaneous latch to the emitted
jump through `PhiView.latch_eq_transfer`. `arm_transfer_iff` characterizes
the complete arm execution at the selected slot. It reaches label two
with the whole tuple from that occurrence and unchanged state. [PhiView](https://github.com/hiloopai/silmaril-lean/pull/3186)

`returns_iff` relates the independent finite returns to finite
`Region.Eval` for every total `Diamond.Model`. The primitive
interpretation preserves ambient state. The regression checks an integer
and a predicate in the same join, different producer schedules in the
two arms, and both branch outcomes in both predecessor orders.
The simultaneous-Phi regression uses two different data sorts and
rejects both mixed-column tuples under either predecessor order.
The profile is one pure acyclic diamond with statically scoped wires.
[Simultaneous-Phi regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/Arms/LambdaSSA/SimultaneousRegression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.SimultaneousRegression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Regression
```
