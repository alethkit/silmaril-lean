# Sequential pure Sea of Nodes diamonds

`Diamond.Arms.Sequential.Graph` connects two arm-local diamonds by the first
join's typed result vector. The second source return relation takes that
vector as its input. A first-stage input can stay live by being included
in the vector. [Arm-local diamond compiler](https://github.com/hiloopai/silmaril-lean/pull/3311)

`Diamond.Arms.Sequential.LambdaSSA.lower` compiles each stage with the
arm-local compiler and uses `Region.linkExits` to attach one continuation
to the first region's exit. The continuation binds the packed join result,
destructures it with binary lets, and renames the second region's inputs
to those bindings. The second CFG's local labels stay scoped to that CFG.
`edge g stage slot` retains the original PhiView occurrence in its stage's
scope, so the same local label and projection can name different transfers.
[The Denotational Semantics of SSA](https://arxiv.org/abs/2411.09347v2)

`lower_hasType` checks the linked region. `continuation_eval` describes
execution from the first join packet. `returns_iff` proves preservation
and reflection of native finite returns, and `lower_eval_iff` identifies
external exit zero, the returned tuple, and unchanged ambient state.
The profile is exactly two sequential acyclic diamonds under one total
pure primitive model.

The regression feeds an integer and a predicate from the first join into
the second CFG. With the initial predicate held true, changing the
integer changes the computed join predicate and the second branch. The
same true projection corresponds to different predecessor slots in the
two stages.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.Regression'
```
