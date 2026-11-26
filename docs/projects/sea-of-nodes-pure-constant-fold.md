# Fold binary word constants in a pure Sea of Nodes table

Simple chapter 8's `Node.peepholeOpt` calls `compute()` and replaces a
nonconstant node when that computation yields a constant type. The
two-constant branches of `AddNode.compute`, `SubNode.compute`, and
`MulNode.compute` use the ordered operands and Java `long` operators.
The Lean pass models those branches with the existing modular
`BitVec 64` evaluator and installs the result as a literal.
[Node.java, lines 243–254](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L254) ·
[AddNode.java, lines 15–23](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L15-L23) ·
[SubNode.java, lines 21–27](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/SubNode.java#L21-L27) ·
[MulNode.java, lines 15–23](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/MulNode.java#L15-L23) ·
[GraphEvaluator.java, lines 75–91](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L75-L91)

`ConstantFold.fold` scans the native `Pure.Program` once in dependency
order. The prefix lookup uses the existing typed origin split to follow
the actual left and right wires. Both lookups must yield literals in
the rewritten prefix. If they do, the pass evaluates the same operation
as native execution and installs a nullary literal at its result slot.
A later binding can immediately read that literal and fold in the same
scan. The output signatures, downstream addresses, and return wire stay
the same.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Defs.lean)

`fold_locals_eq` proves agreement of the full final typed producer store
for every input tuple. `fold_eval_eq` reads the original return from that
store. The proof uses the typed origin split's read theorem to extend
agreement each time the scan adds a binding.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms

open Silmaril.SSA.SeaOfNodes.Pure

private def overflow : Program SubZero.Opcode [] SubZero.word where
  dataflow := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 2) .nil
      (.cons .add (.cons (.output (0 : Fin 2) .head)
        (.cons (.output (1 : Fin 2) .head) .nil)) .nil))
  result := .output (2 : Fin 3) .head

example : (ConstantFold.fold overflow).eval SubZero.model .nil = (1 : BitVec 64) := rfl
```

The regression checks the exact table after folding a chain of addition,
subtraction, and multiplication with wraparound. It retains both a
direct argument read and a later read of an input-dependent producer.
The pass covers explicit literals and literals produced by earlier folds
in this pure word profile. Inferred constants, same-node subtraction,
and removal of unused literal bindings are outside this slice.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.RightIdentityRegression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Regression
```
