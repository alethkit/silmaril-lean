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

## Finite equation observations

```lean
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Thms
```

The existing λSSA observational institution fixes an instruction alphabet,
indexes rooms by scope size, and uses scoped regions and bound environments.
Its observations include fault and divergence. The generated diamond room
varies the native typed primitive signature and compares finite
`Region.Eval` observations on encoded typed input tuples with unit ambient
state. Each side stores the emitted CFG with a propositional generation
witness. `GeneratedRegion.hasType` supplies its original input context and
single typed exit. Satisfaction evaluates the CFG directly using
`instruction` and `inputEnv` from the lowering.
[Existing observational institution](../../Silmaril/SSA/Isotope/Institution/Thms.lean) ·
[Generated equation definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/LambdaSSA/Institution/Defs.lean)

`primitiveFunctor` assigns the actual λSSA primitive alphabet to each
native signature. `mapPrimitive_preservesTypes` checks both operand and
result codes. `lower_map` commutes with the existing `Region.mapInstr`
operation and preserves both successor occurrences into the join.
`instruction_reduct` relates the existing interpretations.
`eval_lower_map` compares every finite observation under the corresponding
reduct, allowing arbitrary ambient state in that theorem.

`lowerEquation_map` commutes with sentence reindexing. `satisfaction`
identifies agreement of the emitted CFGs with the native equation,
using injectivity of the encoded result. `comparison` packages the
translation as an `Inst.CoHom` into the generated room, with models
from the native institution interpreted by the lowering. The room
covers the scheduled pure diamond and its single typed exit.
[Theorem header](../../Silmaril/SSA/SeaOfNodes/Diamond/LambdaSSA/Institution/Thms.lean) ·
[Native institution](sea-of-nodes-diamond-institution.md)

The regression swaps two primitive opcodes, checks both executions with
the false predecessor first, and checks that the two Phi reads are still
distinct occurrences into local label zero.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/LambdaSSA/Institution/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Regression'
```
