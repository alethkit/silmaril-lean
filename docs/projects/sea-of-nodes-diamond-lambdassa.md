# Scheduled Sea of Nodes diamond to λSSA

`Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms` lowers the pure
[diamond from #3135](https://github.com/hiloopai/silmaril-lean/pull/3135)
to an ordinary `Isotope.LambdaSSA.Region.cfg`. Its entry emits one
`let₁` per producer in the graph's dependency order. Each wire reads the
variable of its original input or producer, so shared producers keep a
single binding. The entry case has two successor occurrences into local
label zero. The join unpacks its single parameter and jumps to external
exit zero with the selected result.

`edge g slot` follows the source Region's ordered predecessor slot to
the actual left or right terminator successor. The two successors have the
same target. `phiView g` certifies their packed variable arguments.
`edge_branch` recovers each source slot's branch and `edge_transfer_iff`
uses PhiView latching to identify the exact join label, operand and state
for the selected edge. `lower_hasType` checks the whole emitted region.

For a source `Diamond.Model`, `Primitive.apply` uses the same operation
and declared operand/result sorts. `instruction` relates a packed tuple
of encoded operands to the encoded result of that operation. Data values
carry their source sort as a tag, while predicates use the λSSA sum of
units and ordinary case selection. The relation is deterministic on
encoded inputs and preserves arbitrary ambient state. It is defined per
opcode and admits every total model of the source profile.

`returns_iff` relates the independent `Graph.Returns` to
`Semantics.Region.Eval` of the generated CFG. `lower_eval_iff` also
characterizes the external label, encoded value, and final state of every
target evaluation. The fixture checks both predecessor orders, both
branch arms, a shared producer, and a predicate-valued result.

This bridge covers one pure acyclic diamond with one returned Phi. The
existing RVSDG terminal γ bridge builds a case expression, while the
RVSDG diamond with a join uses a two-exit loop profile. The direct
lowering here exposes the join and its arguments at the selected
occurrence.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.Regression'
```
