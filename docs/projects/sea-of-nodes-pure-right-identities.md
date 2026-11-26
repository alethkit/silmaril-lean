# Checked word addition and multiplication identities

Simple chapter 8's `AddNode.idealize` returns the left input for
`x + 0`, and `MulNode.idealize` does the same for `x * 1`.
Both rules operate on the right operand after the source's usual
ordering. The evaluator uses Java `long` operations in that order.
The Lean word model uses `BitVec 64` addition and multiplication
with the same results modulo `2^64`.
[AddNode.java, lines 27–39](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L27-L39) ·
[MulNode.java, lines 27–40](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/MulNode.java#L27-L40) ·
[GraphEvaluator.java, lines 75–91](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L75-L91)

`SubZero.rewriteRightIdentity?` takes a selected opcode, a binding
in the typed pure producer table, and a proposed literal producer.
The wrapper checks the actual opcode, recovers the ordered operands in
the actual prefix, and requires the right operand to have the exact
typed origin of the corresponding explicit literal. The identity literal
is zero for addition and subtraction and one for multiplication.
The existing typed erasure deletes that binding, reroutes its uses to
the left operand, and reindexes the remaining uses and return.
`SubZero.rewrite?` selects subtraction through the same wrapper.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Pure/SubZero/Defs.lean) ·
[Subtraction case](sea-of-nodes-pure-sub-zero.md) ·
[Typed erasure](sea-of-nodes-gvn-elimination.md)

- `rightIdentity_exact_rhs` proves the exact ordered operand and literal
  checks on acceptance.
- `rightIdentity_count` proves that acceptance deletes exactly one binding.
- `rightIdentity_eval_eq` proves return equality for every typed input.
  The proof discharges local read equality with the corresponding
  right-identity law and reuses the typed erasure theorem to carry that
  equality through the surviving table.

The regression removes the addition feeding a multiplication, then
removes that multiplication and checks the shortened table and shifted
return after both steps. The final addition still wraps the maximum word
plus one to zero. The checker rejects the wrong opcode and a multiplication
whose exact right-hand literal is zero. The scope is nominated right
identities in the pure word fragment. Candidate discovery, inferred
constants, operand commutation, and removal of unused literals are left
to separate passes.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/SubZero/Thms.lean) ·
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/SubZero/RightIdentityRegression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.SubZero.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.RightIdentityRegression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Pure.SubZero.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.RightIdentityRegression
```
