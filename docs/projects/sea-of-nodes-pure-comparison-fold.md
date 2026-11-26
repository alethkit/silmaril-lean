# Fold Simple word comparisons to typed predicates

Simple chapter 8's `BoolNode.compute` evaluates two constant integer
operands in input order. `EQ` compares the words for equality.
`LT` and `LE` compare Java `long` values in signed order. The Java rule
produces integer 0 or 1 and `Node.peepholeOpt` installs the constant.
The native comparison profile represents that Boolean in the
`Diamond.ValueSort.predicate` result slot. Its word operands are
`BitVec 64`, and it uses their signed `slt` and `sle` operations.
[BoolNode.compute, lines 24–35](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/BoolNode.java#L24-L35) ·
[Comparison operators, lines 53–55](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/BoolNode.java#L53-L55) ·
[Node.peepholeOpt, lines 243–249](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L249) ·
[GraphEvaluator, lines 79–83](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L79-L83)

`ConstantFold.Comparison.fold` supplies the comparison rules and
Boolean literal constructor to the existing typed scan. The scan
requires both actual word reads to resolve to known literals in the
rewritten prefix and computes the replacement with the same model used
by evaluation. Arithmetic in this profile delegates to the original
word model.
[Comparison definitions](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/Defs.lean) ·
[Arithmetic fold](sea-of-nodes-pure-constant-fold.md)

`fold_sigs` preserves each output signature. `fold_locals_eq` preserves
the value in every word and predicate producer slot, and `fold_eval_eq`
preserves the native return for every typed input.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/Thms.lean)

The regression folds signed maximum plus one to signed minimum,
compares that word with zero in both operand orders, checks equality
and the inclusive ordering boundary, and retains a comparison with
a program argument. The slice covers only these two-literal
comparison cases. Simple's same-node idealization, Phi rewrites, and
constant-type inference are outside this profile.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.RightIdentityRegression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Regression
```
