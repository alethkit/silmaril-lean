# Checked subtraction-by-zero idealization

Simple chapter 8's `SubNode.idealize` returns its left input when the
right input is integer zero. The rule checks the operand types before
rewriting. Its evaluator reads input 1 minus input 2 using Java
`long` arithmetic. This slice uses the same operand order and
`BitVec 64` modular subtraction in a typed `Pure.Program`.
[Simple SubNode.java at f0a6c675](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/SubNode.java#L31-L40) ·
[Simple evaluator at f0a6c675](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L76-L91)

## Typed rewrite

`SubZero.rewrite?` takes a selected producer and a proposed zero
producer in the same native table. It recovers the subtraction's
actual ordered operands in its prefix. The checker requires an
explicit 64-bit zero literal and compares its typed origin with
the actual right operand. On acceptance, GVN erasure deletes the
subtraction, routes its surviving uses to the left operand, and
reindexes the remaining producer addresses and the return wire.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Pure/SubZero/Defs.lean) ·
[Typed erasure](sea-of-nodes-gvn-elimination.md)

- `rewrite_exact_rhs` gives equality at the exact typed origin of the
  accepted right operand.
- `rewrite_count` proves that the producer count decreases by one.
- `rewrite_eval_eq` proves the same native result on every typed input
  in the modular integer model. The proof uses `BitVec.sub_zero` to
  establish the local read equality required by the existing erasure
  theorem. That theorem carries agreement through the surviving
  producer table and the return.

[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/SubZero/Thms.lean)

## Regression and scope

The fixture rewrites a subtraction consumed by a later noncommutative
use and checks the exact shortened table and shifted return. It checks
wraparound for the resulting subtraction of 1 from 0. The checker
rejects reversed operands, a different zero-producing wire with the
same value, and an actual nonzero literal on the right.

The rewrite covers the pure literal and subtraction profile. The
caller supplies the zero producer, and the check uses its explicit
opcode and origin. Constant inference, branch reasoning, and general
arithmetic reassociation are outside this rule.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/SubZero/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.SubZero.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Pure.SubZero.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.Correctness
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.Regression
```
