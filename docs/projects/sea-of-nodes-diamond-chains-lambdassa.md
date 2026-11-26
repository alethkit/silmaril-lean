# Finite chains of pure Sea of Nodes diamonds

`Diamond.Arms.Chain Op inputs results` types a finite sequence of arm-local
diamonds. The output vector of each stage is the entire input of the next.
The source return relation composes the native per-stage return relations.
An empty chain returns its input vector. [Two-stage bridge](https://github.com/hiloopai/silmaril-lean/pull/3330)

`Diamond.Arms.Chain.LambdaSSA.lower` folds the typed link from the two-stage
bridge. `Sequential.LambdaSSA.link` uses `Region.linkExits` and the existing
tuple decoder to run the compiled suffix from the preceding packed join.
`link_hasType` checks the boundary type. Given finite exit-zero executions
that agree on the intermediate packet, `link_eval_iff` characterizes every
finite observation of the linked region. The empty target is one branch
that packs the input variables and returns them at exit zero.
[The Denotational Semantics of SSA](https://arxiv.org/abs/2411.09347v2)

`edge chain stage slot` lifts the stage's original PhiView occurrence.
The key records its stage position, arm projection, and successor path.
The same projection can select different slots and reach the same local
label in different stages. `edges_from_distinct_stages` distinguishes
those occurrences.

`lower_hasType` checks the folded region. `returns_iff` proves finite-return
preservation and reflection, and `lower_eval_iff` also fixes the exit label
and ambient state. The profile is a finite chain of closed stages under
one total pure model. Each stage keeps its own λSSA label scope.

The regression links three stages through an integer-and-predicate packet
and a predicate-and-two-integers packet. Both intermediate packets drive
later guards. The empty-chain fixture checks identity on the second packet.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.Regression'
```
