# Canonicalize literal-left word multiplication

Simple chapter 8's `MulNode.idealize` swaps a constant left operand
with a nonconstant right operand. It relies on this swap to expose
`1 * x` to its right-identity rule. The native scan does the same
when its typed prefix has a word-literal fact for the actual left
wire and no literal fact for the right wire. Two known operands
still fold to a literal. An already ordered product and a product
of two unknown wires retain their order.
[Pinned MulNode.idealize](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/MulNode.java#L26-L40)

Both `ConstantFold.fold` and `ConstantFold.Comparison.fold` use
the shared rule. It certifies commutativity in the native
`BitVec 64` model and changes the ordered operands at the existing
producer. The typed slots and return wire stay fixed. In both
profiles, `fold_locals_eq` proves equality of the complete producer
store and `fold_eval_eq` proves return equality at every typed
input.
[Arithmetic API](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Thms.lean) ·
[Comparison API](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/Thms.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms

open Silmaril.SSA.SeaOfNodes.Pure

example (p : Program SubZero.Opcode [SubZero.word] SubZero.word) (x : BitVec 64) :
    (ConstantFold.fold p).eval SubZero.model (.cons x .nil) =
      p.eval SubZero.model (.cons x .nil) :=
  ConstantFold.fold_eval_eq p (.cons x .nil)
```

The regression checks both `1 * x` and a downstream literal-left
product. At signed maximum the latter returns `0xfffffffffffffffe`.
It checks the surviving operand order of a right-literal product,
a two-argument product, and an ordered subtraction. It also shows
that the existing right-identity checker accepts the commuted
`x * 1`. Erasure remains a separate operation. The scan registers
this order rule only for multiplication. Simple's negated
subtraction requires a unary minus opcode and its add-spine
reassociation constructs a new intermediate value.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/MulOrderRegression.lean) ·
[Right identities](sea-of-nodes-pure-right-identities.md) ·
[Pinned subtraction](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/SubNode.java#L37-L49) ·
[Pinned add reassociation](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L45-L74)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.MulOrderRegression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.MulOrderRegression
```
