# Propagate a same-source subtraction through the forward scan

Simple chapter 8's `SubNode.compute` returns zero when both inputs
name the same node. `Node.peepholeOpt` turns that result into a literal.
The existing single-binding proof covers the exact typed origin
check for this rule. The forward arithmetic profile now uses the
shared scan's certified same-source rule to install the same zero
at the subtraction's original slot.
[SubNode.compute](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/SubNode.java#L15-L25) ·
[Node.peepholeOpt](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L254) ·
[Single-binding fold](sea-of-nodes-pure-sub-self.md)

`ConstantFold.fold` and `ConstantFold.Comparison.fold` use this
arithmetic rule. A successful replacement updates the literal prefix
before the scan visits the next binding. Distinct sources use the
ordinary ordered two-literal check. The existing `fold_locals_eq`
and `fold_eval_eq` theorems prove that every typed producer value and
the return agree for all inputs.
[Shared arithmetic rules](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Defs.lean) ·
[Comparison theorems](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/Thms.lean)

The regression proves the exact table after one scan. Subtracting an
input-dependent word from itself exposes zero to an addition, which
exposes a literal comparison, which in turn exposes a NOT fold. A
subtraction of distinct runtime sources survives with its consumer.
The shared runtime producer still wraps signed maximum plus one to
signed minimum. The scan covers replacements by literals in existing
slots. Simple's `x + x` to `x * 2` idealization requires a typed
literal-two source and an operand rewrite.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/SubSelfRegression.lean) ·
[AddNode.idealize](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L41-L43)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.SubSelfRegression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.SameSourceRegression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.NegationRegression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubSelf.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.SubSelfRegression
```
