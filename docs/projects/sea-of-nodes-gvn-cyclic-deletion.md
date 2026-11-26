# Delete one unused pure Sea of Nodes header producer

`Cyclic.Deletion.delete?` takes a typed producer reference in a
`Loop.Graph` header. It drops the selected binding and gives its
result no route. Bindings before it already have typed prefixes.
For each surviving later binding, the algorithm traverses the entire
ordered operand tuple and builds a new tuple with shifted typed origins.
At the end it separately routes the guard, every position of the
backedge Phi column, and the exit wire. Any failed route rejects
the deletion. The entry column still reads the original preheader.
[Definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Deletion/Defs.lean) ·
[Checked header substitution](sea-of-nodes-gvn-cyclic-header-use.md)

## Preservation

- `erase_sound` proves that every successful route from the original
  header scope preserves the value read at that typed wire. The proof
  follows header evaluation in dependency order. After a kept binding,
  the two evaluations append equal results of the same operation on
  equal ordered operand tuples.
- `delete_count` gives exact one-binding shrinkage. `delete_initial`
  gives the same initial latches. `delete_step` gives the same activation
  transition from every old latch tuple in every pure total model.
  Its proof gives equality of the guard read, the complete simultaneous
  backedge tuple, and the exit read.
- `delete_evalBackedges` preserves bounded evaluation, including budget
  exhaustion. `delete_returns` preserves and reflects all finite returns.

The deletion requires only the local use check and the typed pure
table. A preceding class-based substitution uses its own activation
invariant to justify redirecting the use. The proof composes the two
contracts in that order.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Deletion/Thms.lean)

## Regression and scope

A duplicate increment is initially live through a guard operand.
`HeaderUse.redirect?` replaces that operand with the earlier increment.
Deleting the duplicate then shrinks the header from four bindings to
three. The guard, a later producer's guard operand, the exit, and both
feedback positions have their expected shifted addresses. The composed
execution takes two backedges and returns 4. Independent variants keep
the candidate live only at the second feedback position or only at the
exit. Both reject deletion. A separate fixture also rejects a producer
used only by the guard.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/Deletion/Regression.lean)

The checker takes one supplied candidate. A use by any surviving
producer counts as live, even when that producer has no uses of its
own. Candidate discovery, repeated deletion, and global dead-code
analysis are outside this slice.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Correctness
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression
```

## Sources

Cliff Click, *Global Code Motion/Global Value Numbering*, PLDI ’95,
§3.1, step 3, replaces uses and removes the redundant node. This
separates that removal into a use-checked operation for one typed
loop header. It reuses the typed origin split from the acyclic
elimination slice. The archived UW PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
[Proceedings](https://doi.org/10.1145/207110.207154) ·
[Archived PDF](https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf) ·
[Acyclic elimination](sea-of-nodes-gvn-elimination.md)

Cliff Click and Michael Paleczny, *A Simple Graph-Based Intermediate
Representation*, IR ’95, §§2.3 and 3.1–3.2, attaches Phi inputs to
ordered Region predecessor occurrences. The use check treats the
complete selected feedback column as a header observation. The
existing loop evaluator still reads that column from one header
snapshot before publishing the updated latches.
[Proceedings](https://doi.org/10.1145/202530.202534) ·
[Loop evaluator](../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean)
