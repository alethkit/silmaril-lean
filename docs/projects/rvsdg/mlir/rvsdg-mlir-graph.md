# Scoped MLIR for acyclic RVSDG

This project-defined dialect lowers the numbered RVSDG fragment with simple
nodes and multi-way γ to the pure MLIR institution's isolated single-block
syntax. The source uses a fixed value alphabet in `Type` and `PEmpty` as
its state alphabet.
A selector for `n` arms has carrier `ULift (Fin n)`. The target uses the source
port sorts in their original order, including selector sorts.

| Operation | Typed interface and denotation |
| --- | --- |
| `rvsdg.simple` | Carries one typed primitive opcode. Operands and results have that opcode's ordered port profiles. It has zero regions and calls the total primitive interpretation. |
| `rvsdg.gamma` | Has a leading selector with at least two alternatives and an ordered payload, with one isolated single-block region per selector value. Every region takes exactly the payload as its block arguments and yields the full result profile. The denotation applies the selected region function to the payload. |

The lowerer extends its local expression environment at each numbered binding
and resolves each wire from an argument or an earlier binding. Each γ region
starts with variables for its own parameters and an empty local environment.
An ordered tuple of expressions represents each block yield. The translation
may duplicate expressions at fan-out and omit unused producer expressions.
`denote_lower` observes the complete ordered result tuple for every input and
every total primitive model. The example uses one shared γ result at two output
ports and checks both selector values, giving result tuples `(6, 6)` and
`(10, 10)`. The opcode-swap example also reinterprets code inside the selected
region and gives `16` at the first result slot.

## MLIR region kinds and scope

Upstream Graph regions admit same-region forward references and cycles. Their
written operation order has no semantic significance. SSACFG regions represent
control flow between blocks and use dominance and terminator successors. In
this slice, the source numbering supplies an acyclic dependency order for
resolving wires, and the target γ chooses a fresh block's yield function.
The target is an expression representation of the project dialect. It has no
upstream RegionKindInterface registration, text parser, CFG edges, trace or
schedule semantics. State, θ feedback, λ, application and recursion require
additional semantics beyond the total scoped model used here.
[LLVM 22.1.0 LangRef, region kinds](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/docs/LangRef.md#regions) ·
[Graph regions](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/docs/LangRef.md#graph-regions) ·
[SSACFG regions](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/docs/LangRef.md#control-flow-and-ssacfg-regions)

## Signature change

For a morphism in the existing RVSDG signature category over the fixed value
alphabet and `PEmpty`, `signatureFunctor` fixes sorts and γ symbols and maps each
`rvsdg.simple` payload by the source opcode map. Lean checks identity and
composition. `lower_map` says that relabelling the numbered graph and then
lowering gives the same expression at each result slot as lowering and then
applying `MLIR.Institution.Term.map`, including inside isolated arms.
`model_reduct` says that constructing the canonical scoped model commutes with
reduction along the same morphism. Extending these results to nested stateless
equations would require a target observation for θ divergence and a matching
reduct.
[Definitions](../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Defs.lean) ·
[Theorems](../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Thms.lean) ·
[Examples](../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Examples.lean)

## Pinned interfaces

- The numbered `Graph`, `Shape.simple`, `Shape.gamma`, `Wires` and `Graph.run`
  are the existing RVSDG API. `Graph.run_toTerm` justifies using the numbered
  graph's inductive linearization. See the corpus references and exact paper
  hash in the RVSDG project page.
  [Source and correspondence](https://github.com/hiloopai/silmaril-lean/tree/2c9e4eec196422e5c4e5f734abacbeb9e865bb2c/Silmaril/SSA/RVSDG) ·
  [RVSDG source citation](../overview.md)
- The scoped target comes from the pure MLIR institution, merged in #2150.
  The later C2 and C3 APIs landed at `527f73ccd44f9f7f775e0aca09e14a06ed1ea1a3`
  and `b2c1cb1a8a5bdfe5ba0b166d16a443b404135f74` respectively. C3 forwards
  regional operations or expands regionless operations. This bridge uses the
  institution's typed `Term`,
  `Block`, `Profile` and `Model` directly.
  [Isolated syntax and model](https://github.com/hiloopai/silmaril-lean/blob/8fdd2cad831858af0f76c994eac4c0877734aac4/Silmaril/SSA/MLIR/Institution/Defs.lean) ·
  [C2 #3012](https://github.com/hiloopai/silmaril-lean/pull/3012) ·
  [C3 #3018](https://github.com/hiloopai/silmaril-lean/pull/3018)
- The nested stateless and interprocedural developments add partial
  observations for θ and ranked dispatch of γ-selected calls inside θ. The
  ordered-runtime chain additionally models an explicit runtime wire. This
  milestone uses the acyclic fragment over total primitives.
  [Stateless #3151](https://github.com/hiloopai/silmaril-lean/commit/5b70a92d9992113a6a097e93b7945d58d9328c4c) ·
  [Ranked calls #3153](https://github.com/hiloopai/silmaril-lean/commit/99794b2634ff52a1442db5178fd52ab071abbc7d) ·
  [Ordered chains #2301](https://github.com/hiloopai/silmaril-lean/commit/ec14ab169556d50ddae25e8f54a0ae01aac7f1f0)
- The independently merged regionless bridge #3133 treats primitive-only
  value graphs. The Sea of Nodes diamond #3135 lowers to the same numbered
  RVSDG graph type and uses the same empty state alphabet.
  [Regionless bridge merge](https://github.com/hiloopai/silmaril-lean/commit/8e906ede8a763ac0d1e19d4840d7782c7215184d) ·
  [Sea of Nodes diamond merge](https://github.com/hiloopai/silmaril-lean/commit/9a7ad8bd413e8d1e5b1e2d353babffe6ea627c67)

## Verify

```sh
lake build --wfail +Silmaril.SSA.RVSDG.MLIR.Graph.Examples
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.MLIR.Graph.Examples
```
