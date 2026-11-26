# Cyclic GVN class values in a pure Sea of Nodes loop

A typed `Activation.View` relates a cyclic producer graph to the ordinary
`Loop.Graph` evaluator. For each represented Phi it identifies the actual
latch port and proves which wires that port reads on entry and on the
backedge. The entry occurrence must read a fixed argument. For each
represented primitive it identifies a producer in the typed header table
and proves equality with that producer's opcode and ordered wire key.
The guard and the return wire must also have corresponding typed sources.
The view is supplied with these proofs. The theorems need correspondence
only for the represented producers, their operands, and the two observations.
[Definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Activation/Defs.lean) ·
[Loop evaluator](../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean) ·
[Stable refinement](sea-of-nodes-gvn-cyclic-fixed-point.md)

## Per-activation agreement

- `View.initial_agrees` establishes the first latch relation from agreement
  at the same typed argument positions. Stable Phi classes agree in the
  entry occurrence, and `Loop.Graph.latch_get` reads that occurrence.
- `View.header_agrees` compares the values read by any two vertices in one
  class, under related inputs and old latches. A Phi reads its old latch.
  Paired primitives have the same typed opcode. Each pair of ordered
  producer operands is earlier in both dependency orders, so the proof
  uses induction on the sum of the two vertex positions. It then applies
  the actual pure total operator to equal typed operand tuples.
- `View.step_agrees` proves equal guard values in the evaluated headers.
  Exit returns the same typed observation. A backedge preserves the latch
  relation because each represented Phi reads its feedback occurrence
  from the same completed header of its own activation, before the new
  latches are visible.

These are relations between two activations of the same loop in any
`Diamond.Model`. They also apply to a single run by relating it to itself.
The premises explicitly identify the typed view, stable partition,
matching input positions, and, for an arbitrary activation, related old
latches. The entry and step theorems establish and preserve the latch
premise from the ordinary execution rules.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Activation/Thms.lean)

## Return-wire substitution and availability

`View.redirectResult` checks stability and compares the existing and
proposed return sources by their typed operand classes. It changes the
return wire only on acceptance. The new wire is typed in the completed
header, where every header producer and latch is available. The guard
and both Phi columns retain their original uses. The proof lifts
per-activation agreement to every budget of `evalBackedges` and to the
same finite `Loop.Graph.Returns` relation.

The regression uses the partition from `FixedPoint.normalize`. Two
independently incremented latches agree at entry and after two taken
backedges. The return changes from producer 0 to
producer 2 and still returns 3. A source of a different class is rejected.
Producer 2 has no wire in the guard's one-binding prefix, even though its
value agrees with producer 0 in the completed activation. Substitution
inside the header would require a typed earlier-prefix wire. More general
control-flow substitutions would also require dominance at the actual use
occurrence. This slice changes the return use and leaves producer removal
and general internal use replacement outside the scope.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/Activation/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation.Correctness
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation.Regression
```

## Sources

Clifford Noel Click Jr., *Combining Analyses, Combining Optimizations*,
Rice PhD dissertation, February 1995, §§4.1–4.2. The proof interprets the
typed form of opcode and ordered-input congruence in the admitted pure
single-loop model. The Rice PDF has SHA-256
`30bec541a006b0a912cb5407b6a37758f8e6c1849ecb7dcfb48cfbf73df3be4c`.
[Rice record](https://hdl.handle.net/1911/16807) ·
[Rice PDF](https://repository.rice.edu/server/api/core/bitstreams/c5ea1ab7-e6c6-41e7-8e06-3cd5b80aeccd/content)

Cliff Click and Michael Paleczny, *A Simple Graph-Based Intermediate
Representation*, IR ’95, §§2.3 and 3.1–3.2, provides the Loop Region and
Phi occurrence correspondence. Simple's chapter 8 evaluator reads the
taken Phi column into a temporary tuple before publishing the new latch
values. The Lean proof uses that same simultaneous update through the
existing `Loop.Graph.latch`.
[Proceedings](https://doi.org/10.1145/202530.202534) ·
[Simple evaluator at the pinned revision](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L93-L151)
