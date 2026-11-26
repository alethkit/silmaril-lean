# Structural GVN refinement for one Sea of Nodes loop

`Silmaril.SSA.SeaOfNodes.GVN.Cyclic` implements one synchronous partition
refinement round and a stability checker over a finite typed producer view
of one Loop Region. It reuses `Diamond.Signature` and the typed RVSDG
`Port` and `Tuple` APIs. Each Phi takes a function argument on entry and
a typed source on the backedge. Pure operands refer to arguments or earlier
producers in the same activation. The ordering certificate ensures that
a producer cycle must traverse a Phi backedge.
[Definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Defs.lean) ·
[Loop model](../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean)

## Checked contract

- `seed_eq_iff` identifies the initial producer classes exactly by profile.
  Pure profiles carry the opcode and the full input and output sorts.
  A Phi profile carries its result sort and belongs to the one implicit
  Region. Arguments have fixed, distinguished addresses from the start.
- `refine_eq_iff` says two labels agree after a round exactly when their
  old labels, profiles, and ordered lists of operand classes agree. Each
  occurrence retains its sort. Argument occurrences keep their input
  index and cannot match producer occurrences. Primitive operands follow
  signature order, with repetitions. Phi operands are in entry, backedge
  order, matching the columns of `Loop.Graph.phiInputs`.
- `checkStable_eq_true_iff` checks that any two producers with the same
  supplied label agree in profile and at every ordered operand occurrence.
  `stable_iff_refine_eq` characterizes this property as preservation of
  the same-class relation by another round. The labels themselves can
  change because each new label is the first vertex with the same key.

[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Thms.lean)

## Regression and semantic boundary

Three Phis share an entry argument. Each feeds a subtraction whose
result returns along that Phi's backedge. In round one, the subtractions
using different arguments separate while the Phis stay together. In
round two the distinction propagates across the backedge and separates
the corresponding Phis. The checker rejects the seed and first round
and accepts the second, retaining the pair of structurally congruent
cycles. A reversed subtraction starts in the same opcode class and
splits on ordered occurrences in round one.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/Regression.lean)

The result certifies structural agreement. To turn it into a semantic
claim about a rewrite requires a typed correspondence to executions of
the source and rewritten loops, including legality of the rewritten
same-activation producer order. On entry, the relation must pair the
actual entry operands at the same typed argument positions and establish
agreement for each corresponding latch. Each activation must then
prove agreement for ordered operands and pure total operator results
in dependency order. Both loops must choose matching control outcomes.
On a backedge the simulation must read the matched feedback occurrences
from the old activation and relate the simultaneously updated latches.
On exit it must relate the observations at their routed result wires.
The checker contains no such execution bridge or rewrite. The slice also
leaves iteration to a fixed point, preheader producers, reachability,
algebraic identities, and worklist complexity outside its scope.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Regression
```

## Sources

Clifford Noel Click Jr., *Combining Analyses, Combining Optimizations*,
Rice PhD dissertation, February 1995, §§4.1–4.2, especially pp. 38–41.
The seed follows the opcode split and the round compares the partition
of the *i*th input, so splits can propagate along uses. The dissertation
uses a smaller-partition worklist for Hopcroft refinement. This round
instead computes keys synchronously by scanning the finite vertex list.
The Rice PDF has SHA-256
`30bec541a006b0a912cb5407b6a37758f8e6c1849ecb7dcfb48cfbf73df3be4c`.
[Rice record](https://hdl.handle.net/1911/16807) ·
[Rice PDF](https://repository.rice.edu/server/api/core/bitstreams/c5ea1ab7-e6c6-41e7-8e06-3cd5b80aeccd/content)

Cliff Click, *Global Code Motion/Global Value Numbering*, PLDI ’95,
§3.1, is the opcode-and-ordered-input key used in the companion acyclic
GVN slice. This round compares input classes in place of producer
addresses and retains argument addresses.
[Proceedings](https://doi.org/10.1145/207110.207154) ·
[Acyclic GVN](sea-of-nodes-gvn-pass.md)
