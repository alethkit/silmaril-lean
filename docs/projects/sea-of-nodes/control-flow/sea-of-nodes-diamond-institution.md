# The Sea of Nodes diamond institution

`Silmaril.SSA.SeaOfNodes.Diamond.Institution.inst` is an institution in the
repository's `Sign ⥤ Room` presentation. The signatures vary the primitive
opcode family over a fixed data-sort alphabet and the distinguished Boolean
predicate sort. A signature morphism maps an opcode at its exact ordered
input sorts and single result sort. Relabelling preserves producer numbers,
wires, the Region predecessor order, and the Phi operands.
[Definitions](../../../../Silmaril/SSA/SeaOfNodes/Diamond/Institution/Defs.lean) ·
[Room interface](../../../../Silmaril/Logic/Institution/Room.lean)

A sentence equates two diamonds with the same ordered input and result types.
A model gives total interpretations to the primitives. Model categories are
discrete. `Equation.Holds` compares the native `Diamond.Graph.denote` results
on every typed input. The reduct of a target model keeps its carriers and
interprets each source opcode by its image. For `h : P ⟶ Q`, the native
dataflow induction gives `denote_mapGraph` and then
`(e.map h).Holds m ↔ e.Holds (reduct h m)`. Identity and composition for
sentence maps and contravariant reducts give the institution's functor laws.
[Theorems](../../../../Silmaril/SSA/SeaOfNodes/Diamond/Institution/Thms.lean)

## Example

The following code swaps two distinct unary primitives at their common
profile. With input 4, the true and false returns are 5 and 8. After
relabelling, the same model gives 8 and 5.

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Defs

namespace Silmaril.SSA.SeaOfNodes.Diamond.Institution

open CategoryTheory
open RVSDG (Tuple)

private abbrev word : ValueSort Unit := .data ()
private abbrev inputs : List (ValueSort Unit) := [.predicate, word]
private abbrev sigs : List (List (Ty Unit)) := [[.value word], [.value word]]

private inductive Arithmetic : Diamond.Signature.{0, 0} Unit
  | inc : Arithmetic [word] word
  | double : Arithmetic [word] word

private abbrev sig : Signature.{0, 0} Unit := ⟨Arithmetic⟩

private def arithmetic : Model.{0, 0, 0} sig.op where
  value _ := Nat
  run
    | .inc, .cons n .nil => Nat.succ n
    | .double, .cons n .nil => Nat.add n n

private def swap : sig ⟶ sig :=
  ⟨fun
    | .inc => .double
    | .double => .inc⟩

private def diamond (onTrue onFalse : Arithmetic [word] word) : Graph sig.op inputs sigs word where
  dataflow :=
    .cons onTrue (.cons (.arg (.tail .head)) .nil)
      (.cons onFalse (.cons (.arg (.tail .head)) .nil) .nil)
  predicate := .arg .head
  phi := ⟨⟨.onFalse⟩, fun
    | .first => .output (1 : Fin 2) .head
    | .second => .output (0 : Fin 2) .head⟩

private def entry (pred : Bool) : Tuple (Val arithmetic.value) (dataPorts inputs) :=
  .cons ⟨pred⟩ (.cons (4 : Nat) .nil)

private def graph := diamond .inc .double

#eval ([graph.denote arithmetic (entry true), graph.denote arithmetic (entry false),
  (mapGraph swap graph).denote arithmetic (entry true),
  (mapGraph swap graph).denote arithmetic (entry false)] : List Nat)

end Silmaril.SSA.SeaOfNodes.Diamond.Institution
```

The regression also identifies both opcodes with `inc`. An equation that
fails in the original model then holds after translation, and the
satisfaction theorem proves the corresponding claim in the reduct. It
also checks the bundled institution's sentence map and model reduct.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/Institution/Regression.lean)

The profile has one pure, total, acyclic diamond and one returned Phi.
For a later bridge naturality theorem at `Type`, lift a source map to RVSDG
by mapping `Diamond.Opcode.pure` through its opcode image and fixing
`Diamond.Opcode.dispatch`. Prove that relabelling commutes with diamond
lowering and its induced model, then use the scoped `signatureFunctor`,
`lower_map` and `model_reduct` from #3162 for the corresponding MLIR squares.
[Source diamond](https://github.com/hiloopai/silmaril-lean/pull/3135) ·
[Scoped signature functor](../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Thms.lean) ·
[Scoped diamond comparison](sea-of-nodes-diamond-mlir.md)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.Institution.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Institution.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Diamond.Institution.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```

The underlying sources are Click and Paleczny's graph-based IR and Goguen
and Burstall's institution theory.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Institutions](https://doi.org/10.1145/147508.147524)
