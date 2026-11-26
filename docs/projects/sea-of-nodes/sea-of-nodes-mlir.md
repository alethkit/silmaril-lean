# Sea of Nodes pure producers to scalar MLIR

`Silmaril.SSA.SeaOfNodes.MLIR.lower` takes a `Diamond.Dataflow` with word
inputs and a selected word-valued result wire. The common operations are
constants, addition and multiplication on positive-width bit vectors.
Their target counterparts are `arith.constant`, `arith.addi` and
`arith.muli`, with empty overflow flags. The lowering emits one
`Arith.Block.letOp` per producer in table order. Uses of a shared producer refer
to its one binding. `lower_denote` proves equality of the selected source
value and the target block result on every typed input, using the existing
`Diamond.Dataflow.eval` and `Diamond.read`.
[Definitions](../../../Silmaril/SSA/SeaOfNodes/MLIR/Defs.lean) ·
[Theorem](../../../Silmaril/SSA/SeaOfNodes/MLIR/Thms.lean)

## Upstream interface boundary

- The Sea of Nodes diamond in [#3135][diamond-pr] at
  `2831cc375cec231ab1569cd145cefff82a1972a4`, merged at
  `9a7ad8bd413e8d1e5b1e2d353babffe6ea627c67`, has a topologically enumerated
  pure producer table. Its whole-graph lowering adds an
  `Opcode.dispatch` that returns `[.control 2, .value out, .value out]` and
  a `Shape.gamma` that consumes the tag to select a predecessor-specific Phi
  operand. Even `Diamond.Dataflow.lower` uses the whole `Diamond.Opcode`
  signature, which includes dispatch.
  [Producer types and evaluator][diamond-data] ·
  [Dispatch profile][diamond-dispatch] · [Phi lowering][diamond-phi]
- The RVSDG bridge in [#3133][rvsdg-pr] at
  `4cd40b5d3b8ab153b00760af20543560a2e8e016`, merged at
  `8e906ede8a763ac0d1e19d4840d7782c7215184d`, requires a `ProfileMap` for
  the entire source dialect. Its `MatchedOp.symbol` constructor has
  value-only input and output port lists, so it supplies no image at the
  dispatch profile. The merged MLIR institution also represents regions as
  isolated, single-block expression tuples; region arities alone supply
  no CFG branches, joins or control selection. The pure producer bridge
  calls the Sea of Nodes evaluator directly and targets the existing
  `Arith.Block` API.
  [RVSDG profile map][rvsdg-profile] · [MLIR term and block types][institution]
- The target block came from [#2133][arith-pr], merged at
  `01b6b841efed69df42d39176333a54332e4da049`. The typed scalar facade in
  [#3012][facade-pr] merged at `527f73ccd44f9f7f775e0aca09e14a06ed1ea1a3`.
  The operation interpretation interfaces in [#3018][interpretation-pr]
  merged at `b2c1cb1a8a5bdfe5ba0b166d16a443b404135f74`.
  [Scalar block and denotation][arith-block]

## Graph regions and SSACFG

In an MLIR graph region, same-region SSA uses may refer forward and form
cycles. The containing operation supplies the semantics. Textual operation
order does not provide a control schedule. A Sea of Nodes `Region` names a
control join with predecessor-indexed Phi operands. Encoding such a graph
inside an MLIR graph region would require an operation whose semantics
accounts for those edges and their selection.
[MLIR Language Reference, Graph Regions][graph-regions] · [Click and Paleczny, §§2.1–2.5 and §3.1][click-paleczny]

An MLIR SSACFG region executes each block in order. Terminators select
successors, and dominance controls the availability of SSA values. In the
one-block Arith slice, the input table already orders every producer after
its dependencies, and each emitted operation refers to block arguments or
earlier bindings. For a control-bearing graph, a lowering must also choose
legal blocks for floating operations, check dominance and scope, and pass
Phi operands along their specific incoming edges to destination block
arguments. Pinned operations require their control placement. A schedule
that moves potentially trapping or effectful operations must preserve
their guards and ordering obligations, including relevant memory
dependencies. Fixed-width flag-free addition and multiplication are
total and have no effects in this model.
[MLIR Language Reference, SSACFG][ssacfg] · [MLIR Side Effects & Speculation][effects] ·
[Click, Global Code Motion/Global Value Numbering, §§2.1–2.4][gcm]

The theorem covers a selected result wire and a typed Arith block.
A graph-region encoding, the diamond's If/Region/Phi execution, scheduling
an unordered graph, effects, and verification of serialized MLIR remain
outside its scope. The sharing regression checks the emitted binding
structure and a mixed-width input with 8-bit wraparound.
[Regression](../../../Silmaril/Proofs/SSA/SeaOfNodes/MLIR/Regression.lean)

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.MLIR.Thms +Silmaril.Proofs.SSA.SeaOfNodes.MLIR.Regression
```

## Reference versions

- Clifford Click and Michael Paleczny, *A Simple Graph-Based Intermediate
  Representation*, IR ’95, pp. 35–49. The workshop PDF SHA-256 is
  `9c12e5cd0ee54beb51436b25aec73c45855bb0eb5bafaa76ee4135edeadca17c`.
  [DOI][click-paleczny] · [Artifact and source inventory][inventory]
- Cliff Click, *Global Code Motion/Global Value Numbering*, PLDI ’95,
  pp. 246–257. The archived UW PDF SHA-256 is
  `9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
  [DOI][gcm] · [Artifact and source inventory][inventory]
- LLVM 21.1.0 at `3623fe661ae35c6c80ac221f14d85be76aa870f1`.
  [Region kinds][graph-regions] · [Arith constant/add/multiply definitions][arith-ops] ·
  [Side effects and speculation][effects]

[diamond-pr]: https://github.com/hiloopai/silmaril-lean/pull/3135
[diamond-data]: https://github.com/hiloopai/silmaril-lean/blob/2831cc375cec231ab1569cd145cefff82a1972a4/Silmaril/SSA/SeaOfNodes/Diamond/Defs.lean#L69-L80
[diamond-dispatch]: https://github.com/hiloopai/silmaril-lean/blob/2831cc375cec231ab1569cd145cefff82a1972a4/Silmaril/SSA/SeaOfNodes/Diamond/Defs.lean#L175-L203
[diamond-phi]: https://github.com/hiloopai/silmaril-lean/blob/2831cc375cec231ab1569cd145cefff82a1972a4/Silmaril/SSA/SeaOfNodes/Diamond/Defs.lean#L225-L254
[rvsdg-pr]: https://github.com/hiloopai/silmaril-lean/pull/3133
[rvsdg-profile]: https://github.com/hiloopai/silmaril-lean/blob/4cd40b5d3b8ab153b00760af20543560a2e8e016/Silmaril/SSA/RVSDG/MLIR/Regionless/Defs.lean#L23-L45
[arith-pr]: https://github.com/hiloopai/silmaril-lean/pull/2133
[facade-pr]: https://github.com/hiloopai/silmaril-lean/pull/3012
[interpretation-pr]: https://github.com/hiloopai/silmaril-lean/pull/3018
[institution]: https://github.com/hiloopai/silmaril-lean/blob/b2c1cb1a8a5bdfe5ba0b166d16a443b404135f74/Silmaril/SSA/MLIR/Institution/Defs.lean#L78-L91
[arith-block]: https://github.com/hiloopai/silmaril-lean/blob/01b6b841efed69df42d39176333a54332e4da049/Silmaril/SSA/MLIR/Arith/Defs.lean#L53-L78
[inventory]: https://github.com/hiloopai/silmaril-lean/blob/9f0b659d1ae77198596c284feb7adf4eabf03da5/docs/projects/sea-of-nodes.md#editions-and-source-boundaries
[graph-regions]: https://github.com/llvm/llvm-project/blob/3623fe661ae35c6c80ac221f14d85be76aa870f1/mlir/docs/LangRef.md#graph-regions
[ssacfg]: https://github.com/llvm/llvm-project/blob/3623fe661ae35c6c80ac221f14d85be76aa870f1/mlir/docs/LangRef.md#control-flow-and-ssacfg-regions
[effects]: https://github.com/llvm/llvm-project/blob/3623fe661ae35c6c80ac221f14d85be76aa870f1/mlir/docs/Rationale/SideEffectsAndSpeculation.md
[arith-ops]: https://github.com/llvm/llvm-project/blob/3623fe661ae35c6c80ac221f14d85be76aa870f1/mlir/include/mlir/Dialect/Arith/IR/ArithOps.td#L162-L375
[click-paleczny]: https://doi.org/10.1145/202529.202534
[gcm]: https://doi.org/10.1145/207110.207154
