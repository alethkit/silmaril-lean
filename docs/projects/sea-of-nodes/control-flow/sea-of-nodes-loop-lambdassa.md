# Sea of Nodes counted swap in λSSA

`Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Thms` compares a scheduled
counted-swap instance of the [source-native loop in #3192](https://github.com/hiloopai/silmaril-lean/pull/3192)
with an ordinary `Isotope.LambdaSSA.Region.cfg`. The admitted graph has
inputs `limit, a, b` and a carried tuple `(a, b, i)`. A seed operation
initializes `i`. The header computes a predicate, next index and result
in order. True sends `(b, a, next)` to the same header, and false returns
the result computed from the old pair.

The preheader and true case arm are distinct occurrences at local label
zero. `phiView` transposes their packed header arguments.
`edge_branch`, the round-trip equalities and `edge_transfer_iff` check
the transfers through PhiView. The target header destructures its packed
parameter once on each activation. Its false branch emits raw label one,
which `Region.Follow.exit` maps to external label zero.

Source and target share any total `Diamond.Model Op` for the four
primitive profiles. `run` computes one primitive on its encoded operands,
and the instruction relation leaves arbitrary ambient state unchanged.
`lower_hasType` checks the emitted CFG. `follow_iff` relates finite
`Region.Follow` evidence from the header to the source's counted
`ReturnsAfter`, including an immediate exit with zero backedges.
`returns_iff` and `mem_denote_iff` compare actual `Region.Eval` at
external exit zero with the independent source return relation and partial
denotation.

The two incoming occurrences and old-tuple reads follow
[Click and Paleczny, IR ’95 §§2.3 and 3.1–3.2](https://doi.org/10.1145/202530.202534)
and the pinned [Simple loop evaluator](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L93-L151).
The Lean fixtures use natural-number primitives. They check the immediate
exit, the swapped feedback tuple, and complete runs with zero to three
backedges. The theorem covers this fixed schedule for every input and
total primitive model of the profile. Its observation is finite return.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Regression'
```
