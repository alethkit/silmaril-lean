# Fold Boolean negation of a Simple comparison

Simple chapter 8 parses `a != b` as `NotNode(BoolNode.EQ(a, b))` and
runs the peephole on the equality before the negation. The evaluator
represents comparison results as integer 0 or 1. `NotNode.compute`
maps a constant zero to 1 and any other constant to 0. The typed slice
uses the native Boolean predicate produced by a comparison, so those
two cases are `false → true` and `true → false`.
[Parser.java, lines 384–391](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/Parser.java#L384-L391) ·
[NotNode.java, lines 15–20](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/NotNode.java#L15-L20) ·
[GraphEvaluator.java, lines 79–88](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L79-L88)

`ConstantFold.Comparison.fold` reads the actual operand from the typed
literal prefix. After a comparison folds, the next binding can read
its Boolean result in the same scan. A known operand allows the native
negation evaluator to produce a Boolean literal at the original slot.
A comparison depending on an argument supplies no literal fact, so
its negation remains for execution. The scan traverses the operand
tuple in signature order and uses the same proof for word and Boolean
operands.
[Comparison profile](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/Defs.lean) ·
[Shared scan](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Defs.lean)

`fold_sigs`, `fold_locals_eq`, and `fold_eval_eq` give the same typed
slots, producer values, and native return for every input. The fixture
checks the exact table for `7 != 8`, a second negation of that folded
predicate, and a retained `x != 7` that distinguishes two inputs.
The profile admits negation at the Boolean predicate sort. For
constant If/Phi selection, the separate diamond branch fold returns the
selected predecessor's value.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/Thms.lean) ·
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/NegationRegression.lean) ·
[Known diamond branch fold](rice-diamond-sccp-branch-fold.md)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.NegationRegression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.NegationRegression
```
