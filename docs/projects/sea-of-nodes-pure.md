# Pure-value Sea of Nodes

A `Pure.Program` consists of a typed producer table and one returned wire.
The table orders each producer after its dependencies. An operand can read
an entry argument or a numbered earlier result, and several operands can
read the same wire. `Program.eval` runs the source table with total primitive
functions and reads the returned value. [Definitions](../../Silmaril/SSA/SeaOfNodes/Pure/Defs.lean)

The following example uses eight-bit modular arithmetic. The third binding
reads both operands from vertex 1, which computes `x + 1` once.

```lean
module

import Silmaril.SSA.SeaOfNodes.Pure.Thms
meta import Silmaril.SSA.SeaOfNodes.Pure.Defs

open Silmaril.SSA.SeaOfNodes
open Diamond (Model ValueSort)

private abbrev byte : ValueSort Unit := .data ()

private inductive ByteOp : List (ValueSort Unit) → ValueSort Unit → Type where
  | one : ByteOp [] byte
  | add : ByteOp [byte, byte] byte

private def byteModel : Model ByteOp where
  value _ := BitVec 8
  run
    | .one, .nil => (1 : BitVec 8)
    | .add, .cons x (.cons y .nil) => BitVec.add x y

-- Vertex 0 produces 1, vertex 1 produces x + 1, and vertex 2 reads vertex 1 twice.
private def doubledNext : Pure.Program ByteOp [byte] byte where
  dataflow :=
    .cons .one .nil <|
    .cons .add (.cons (.arg .head) (.cons (.output ⟨0, by decide⟩ .head) .nil)) <|
    .cons .add (.cons (.output ⟨1, by decide⟩ .head) (.cons (.output ⟨1, by decide⟩ .head) .nil)) .nil
  result := .output ⟨2, by decide⟩ .head

#eval (doubledNext.eval byteModel (.cons (20 : BitVec 8) .nil)).toNat

#eval (doubledNext.eval byteModel (.cons (255 : BitVec 8) .nil)).toNat

example (x : BitVec 8) :
    doubledNext.lower.run (Pure.toRVSDGModel byteModel) (.cons x .nil) =
      .cons ((x + 1) + (x + 1)) .nil :=
  doubledNext.lower_run byteModel (.cons x .nil)
```

The two evaluations print `42` and `0`. `Program.lower_run` works for any
typed input and source model. `Equation.Holds` compares native source
evaluations across all inputs. `Equation.satisfaction` transfers that
comparison in both directions to `Equation.toRVSDG` in the induced
`Pure.toRVSDGModel`. The lowered program emits only simple value-port
vertices and keeps their original order and wires. The modeled fragment is
straight-line and pure, with one returned value.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Pure/Thms.lean)

The producer table and source evaluator currently live in
`SeaOfNodes.Diamond.Defs`. The pure facade imports that header and uses
its `Dataflow`, typed origins and evaluator directly. A later extraction
could give both clients a common dataflow header and share the primitive
emitter. The [Sea of Nodes inventory](sea-of-nodes.md) records the source
literature and the broader proof obligations.

Run the [regression](../../tests/ssa/SeaOfNodesPure.lean) from the repository root.

```sh
make check CHECK_TARGETS=+Silmaril.SSA.SeaOfNodes.Pure.Thms
```
