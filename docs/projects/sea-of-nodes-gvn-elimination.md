# Removing one checked redundant Sea of Nodes producer

`Silmaril.SSA.SeaOfNodes.GVN.Elimination.eliminate?` substitutes an
accepted earlier representative throughout the remaining pure producer
table and removes the candidate binding. It implements the replacement
and deletion step in Click’s PLDI ’95 §3.1 for one supplied pair.
[Definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Elimination/Defs.lean) ·
[Representative checker](sea-of-nodes-gvn.md)

## Admission and routing

The caller names two actual producers of the same sort in one typed,
acyclic `Diamond.Dataflow` table. The candidate determines the exact
scope where its operands are read. The replacement must be a wire of
the candidate’s result sort in that scope. The checker requires
`checkRepresentative` to accept the earlier producer and verifies that
the replacement’s address in the original final scope identifies that
same representative. A rejected proposal returns `none`.

The prefix of the table stays in its original order with its original
operands. At the deleted binding, the substitution maps that result to
the supplied prefix wire. The rewrite traverses the suffix in order,
replacing the typed operand wires of each kept binding and extending
the substitution with that binding’s new output positions. Each
substitution acts on the current prefix, so a rewritten operand can only
read an argument or a producer already in scope. The final substitution
maps all original wires, including the selected return wire, into the
shorter table. Later producer numbers shift by one.

## Verified contract

- `eliminate_sound` proves that every original typed wire reads the same
  value after the returned substitution in every pure total model, for
  every input and initial prefix assignment. This includes the deleted
  result, all surviving producers, and the final return wire. The proof
  uses `checkRepresentative_sound` to justify substitution at the deletion
  point and propagates the read invariant through each surviving binding.
- `eliminate_size` proves that a successful rewrite removes exactly one
  producer from the supplied table.

[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Elimination/Thms.lean) ·
[Representative soundness and transport](../../Silmaril/SSA/SeaOfNodes/GVN/Thms.lean)

The regression starts with two identical subtractions. Two later bindings
read the duplicate, and the final binding also reads a producer whose
number shifts. The resulting three-binding table is checked against a
concrete typed table with both uses visibly redirected. The mapped final
wire still reads `-3` for inputs `10` and `3`. A same-sort prefix wire
with the wrong address is rejected. [Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Elimination/Regression.lean)

The result covers one deletion and its output routing in the pure
acyclic table. Representative discovery, algebraic identities, and
cyclic congruence refinement remain separate. Control placement and
effects are outside this table’s model.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Regression'
```

## Source

Cliff Click, *Global Code Motion/Global Value Numbering*, PLDI ’95,
pp. 246–257, §3.1, step 3. The archived UW PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
[Proceedings](https://doi.org/10.1145/207110.207154) ·
[Archived PDF](https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf)
