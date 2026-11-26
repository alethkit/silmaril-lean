# Fold comparisons of the same word source

Simple chapter 8's `BoolNode.idealize` tests whether inputs 1 and 2
name the same node. It then returns the comparison's result on equal
words as a constant. Equality and signed less-than-or-equal return
true, and signed less-than returns false. These are the three
comparison opcodes in the existing native predicate profile.
[BoolNode.idealize, lines 37–48](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/BoolNode.java#L37-L48) ·
[Operators, lines 53–55](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/BoolNode.java#L53-L55)

`ConstantFold.Comparison.fold` compares the actual two typed word
origins in the current prefix. When their addresses agree, the
existing typed address theorem identifies the wires. The rule then
uses the operator's certified result on any repeated word value.
Distinct sources fall through to the ordinary two-literal check.
The shared scan installs each Boolean literal in the original slot,
where a later operation can use it in the same scan.
[Shared scan](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Defs.lean) ·
[Comparison profile](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/Defs.lean)

`fold_sigs`, `fold_locals_eq`, and `fold_eval_eq` preserve the typed
layout, all producer values, and the return for every input. The
regression folds repeated reads of a runtime argument and a producer,
then folds a negation of the new predicate. It retains a comparison
of distinct runtime wires even when a particular input makes their
values equal. The producer also exercises signed maximum plus one,
which wraps to the minimum signed word. The slice covers exact
same-source comparisons in the pure table.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/Thms.lean) ·
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/SameSourceRegression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.SameSourceRegression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.NegationRegression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.SameSourceRegression
```
