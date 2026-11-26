# The pure Sea of Nodes diamond in scoped MLIR

The bridge lowers the existing `Diamond.Graph` through its numbered RVSDG
graph into the project-defined scoped MLIR dialect. For total source models
with carrier and opcode types in `Type`, the lowered block denotes a value
exactly when the diamond has a finite return of that value. `denote_eq`
compares the block directly with `Diamond.Graph.denote`. The proof
uses `Diamond.Graph.lower_returns_iff` for the source return relation and
`RVSDG.MLIR.Graph.denote_lower` for the target's ordered results, then
projects the unique result. [Definitions][bridge] · [Theorem][theorem]

For two diamonds with the same ordered entry and result types,
`lowerEquation` gives an MLIR block equation. The `satisfaction` theorem
equates validity in `Diamond.MLIR.model m` with agreement of the diamonds'
native denotations on every typed input. The proof converts between ordered
source tuples and the target's finite input assignments.
[Definitions][bridge] · [Theorems][theorem]

## Scope and region kind

The diamond has one If, a Region with two predecessor slots and one returned
Phi. The source table is already enumerated in dependency order and admits
pure total producers. Its dispatch converts the Boolean predicate to a finite
selector, with true at 0 and false at 1, and forwards the two Phi operands in
Region order. The two scoped γ bodies receive the operands as explicit
parameters and each returns the capture for its predecessor's Region slot.
The target's expressions may
duplicate a shared producer or omit an unused producer. The observation
covers the returned value.
[Diamond source and dispatch][diamond-defs] · [Scoped target model][scoped-model]

MLIR Graph regions admit same-region forward references and cycles. The
containing operation defines their behavior, and textual order does not supply
a schedule. In an SSACFG region, operations execute in block order,
terminators select successor blocks, and SSA dominance and scope determine
which values are available.
Here the project dialect gives γ a pure isolated-block interpretation. A Sea
of Nodes Region is a control join with predecessor-indexed Phi operands.
This proof leaves an upstream MLIR RegionKindInterface registration and an
SSACFG lowering outside its scope.
[MLIR Graph regions][graph-regions] · [MLIR SSACFG regions][ssacfg] ·
[Click and Paleczny, §§2.1–2.5 and §3.1][click-paleczny]

For general Sea of Nodes lowering, floating nodes need legal placement and
dominance checks, a Phi operand is available on its own incoming edge, and
pinned nodes retain their control attachment. Speculation across control
requires preservation of definedness and effects, including memory ordering.
The eager source evaluation here applies only to its pure total producer
table. Loops, arbitrary schedules, partial primitives, effects and emitted
MLIR text require further interfaces and proofs.
[Click, Global Code Motion/Global Value Numbering, §§2.1–2.4][gcm] ·
[MLIR Side Effects & Speculation][effects] · [Sea of Nodes source inventory][inventory]

## Pinned interfaces

- The diamond and `Graph.lower_returns_iff` come from #3135 at
  `2831cc375cec231ab1569cd145cefff82a1972a4`, merged at
  `9a7ad8bd413e8d1e5b1e2d353babffe6ea627c67`.
  [Definitions][diamond-defs] · [Return theorem][diamond-theorem]
- #3162 initially used `Empty` at `6c318c923a18b46f6974d0c0564ed9da0310636b`.
  The composition uses `4720c4a7a5479367ac0b35e7b6fc7a975da2002b`, merged
  at `8ae0dd564b50ce0b1b86082e581cd36608a5e15c`. At the common universe
  `Type`, both sides use `PEmpty.{1}` and the same ordered port alphabet.
  The constructor `source Op := ⟨Opcode Op⟩` checks that alignment.
  `model m` passes `m.toRVSDG` directly to the scoped model constructor.
  Its carriers are `Diamond.Val m.value`, and only the positional tuple
  conversion is needed to pass an input to the MLIR evaluator.
  [Initial alphabet][initial-alphabet] · [Aligned alphabet][aligned-alphabet] ·
  [Scoped theorem][scoped-theorem]
- The primitive-only regionless bridge #3133 at
  `4cd40b5d3b8ab153b00760af20543560a2e8e016` uses value-only profiles. The
  diamond dispatch returns a control port and its γ consumes it. The
  scoped MLIR target uses the isolated expression-block API from #2150,
  merged at `8fdd2cad831858af0f76c994eac4c0877734aac4`.
  [Regionless profile][regionless] · [Merged MLIR syntax][institution]
- The scoped dialect's signature functor and renaming laws concern the RVSDG
  signature category. A Sea of Nodes institution comparison would also need
  source signature maps, native model reducts and naturality of the sentence
  and model maps.
  [Scoped signature functor and laws][scoped-theorem]

## Example

Copy this into a Lean file. The input is a Boolean predicate followed by
the data value 4. The true arm returns the shared `inc` result and the
false arm uses that result twice. The example prints `[5, 10, 5, 10]` for
true then false at each of the two Region orders.

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Defs

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR

open RVSDG (Origin Tuple extend)

private abbrev word : ValueSort Unit := .data ()
private abbrev inputs : List (ValueSort Unit) := [.predicate, word]
private abbrev sigs : List (List (Diamond.Ty Unit)) := [[.value word], [.value word]]

private inductive Arithmetic : Diamond.Signature.{0, 0} Unit where
  | inc : Arithmetic [word] word
  | add : Arithmetic [word, word] word

private def arithmetic : Model Arithmetic where
  value _ := Nat
  run
    | .inc, .cons n .nil => Nat.succ n
    | .add, .cons x (.cons y .nil) => Nat.add x y

private abbrev ResultWire := Origin (dataPorts inputs) (extend [] sigs) (.value word)

private def shared : ResultWire := .output (0 : Fin 2) .head
private def doubled : ResultWire := .output (1 : Fin 2) .head

private def diamond (first : Projection) (onFalse : ResultWire) :
    Graph Arithmetic inputs sigs word where
  dataflow :=
    .cons .inc (.cons (.arg (.tail .head)) .nil)
      (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  predicate := .arg .head
  phi := ⟨⟨first⟩, match first with
    | .onTrue => fun | .first => shared | .second => onFalse
    | .onFalse => fun | .first => onFalse | .second => shared⟩

private def entry (b : Bool) : Tuple (Val arithmetic.value) (dataPorts inputs) :=
  .cons ⟨b⟩ (.cons (4 : Nat) .nil)

#eval ([denote arithmetic (diamond .onTrue doubled) (entry true),
  denote arithmetic (diamond .onTrue doubled) (entry false),
  denote arithmetic (diamond .onFalse doubled) (entry true),
  denote arithmetic (diamond .onFalse doubled) (entry false)] : List Nat)

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR
```

The regression also checks a shared result on both incoming slots, a valid
equation between the two predecessor orders, and a refuted equation that
changes the false result. [Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.MLIR.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```

[bridge]: ../../../../Silmaril/SSA/SeaOfNodes/Diamond/MLIR/Defs.lean
[theorem]: ../../../../Silmaril/SSA/SeaOfNodes/Diamond/MLIR/Thms.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/MLIR/Regression.lean
[diamond-defs]: https://github.com/hiloopai/silmaril-lean/blob/2831cc375cec231ab1569cd145cefff82a1972a4/Silmaril/SSA/SeaOfNodes/Diamond/Defs.lean
[diamond-theorem]: https://github.com/hiloopai/silmaril-lean/blob/2831cc375cec231ab1569cd145cefff82a1972a4/Silmaril/SSA/SeaOfNodes/Diamond/Thms.lean#L37-L42
[initial-alphabet]: https://github.com/hiloopai/silmaril-lean/blob/6c318c923a18b46f6974d0c0564ed9da0310636b/Silmaril/SSA/RVSDG/MLIR/Graph/Defs.lean#L19-L20
[aligned-alphabet]: https://github.com/hiloopai/silmaril-lean/blob/4720c4a7a5479367ac0b35e7b6fc7a975da2002b/Silmaril/SSA/RVSDG/MLIR/Graph/Defs.lean#L20-L21
[scoped-model]: https://github.com/hiloopai/silmaril-lean/blob/4720c4a7a5479367ac0b35e7b6fc7a975da2002b/Silmaril/SSA/RVSDG/MLIR/Graph/Defs.lean#L72-L78
[scoped-theorem]: https://github.com/hiloopai/silmaril-lean/blob/4720c4a7a5479367ac0b35e7b6fc7a975da2002b/Silmaril/SSA/RVSDG/MLIR/Graph/Thms.lean
[regionless]: https://github.com/hiloopai/silmaril-lean/blob/4cd40b5d3b8ab153b00760af20543560a2e8e016/Silmaril/SSA/RVSDG/MLIR/Regionless/Defs.lean#L37-L45
[institution]: https://github.com/hiloopai/silmaril-lean/blob/8fdd2cad831858af0f76c994eac4c0877734aac4/Silmaril/SSA/MLIR/Institution/Defs.lean#L78-L91
[graph-regions]: https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/docs/LangRef.md#graph-regions
[ssacfg]: https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/docs/LangRef.md#control-flow-and-ssacfg-regions
[effects]: https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/docs/Rationale/SideEffectsAndSpeculation.md
[inventory]: https://github.com/hiloopai/silmaril-lean/blob/9f0b659d1ae77198596c284feb7adf4eabf03da5/docs/projects/sea-of-nodes.md#editions-and-source-boundaries
[click-paleczny]: https://doi.org/10.1145/202529.202534
[gcm]: https://doi.org/10.1145/207110.207154
