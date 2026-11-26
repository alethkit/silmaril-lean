# Scoped MLIR-style lowering for stateless RVSDG feedback

The source is a numbered `NestedTheta.Graph` admitted by the stateless
institution's `NoState` predicate. It can have primitive, γ and θ bindings at
any nesting depth. Primitive interpretations are total over the fixed value
alphabet. A θ may take indefinitely many body activations, so the observable
result is a partial, ordered tuple.

The target is a project-defined, single-block region with explicit SSA
bindings. Group zero is the ordered block argument tuple. Every binding adds
one group of result names, with references to a particular port of an earlier
group. Each nested region opens with only its own argument group. The lowering
reuses the corpus's typed ports, tuples and reference lookup and gives every
source binding a target binding, including bindings with unused results or
empty result profiles.

| Binding | Execution |
| --- | --- |
| Primitive | Evaluate the primitive once on its typed operands and bind its entire result tuple. |
| γ | Use the leading selector to choose a single isolated arm. Pass the remaining tuple as its ordered arguments and bind its yield. |
| θ | Invoke the isolated body on the seed carry. The body yields a two-way selector followed by the updated carry. Selector `1` restarts with that carry, and selector `0` supplies that carry to the continuation. The first activation is mandatory. |

The [acyclic scoped bridge](rvsdg-mlir-graph.md) introduced typed isolated γ
arms and ordered yields for the total fragment. Its expression representation
can omit unused producers. Feedback uses explicit bindings because omitting
an unused θ would discard its execution. The merged [SCF while to CF](https://github.com/hiloopai/silmaril-lean/pull/3167)
and [SCF if with while to CF](https://github.com/hiloopai/silmaril-lean/pull/3198)
use bitvector widths and an `i1` test. The [CF switch and assert fragment](https://github.com/hiloopai/silmaril-lean/pull/3184)
also works over width-indexed operands. This adapter retains the source's
arbitrary value sorts, multi-result primitives and finite multi-way selectors.
It has its own finite-return semantics and requires only merged dependencies.

## Checked observations

`Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.returns_lower_iff` preserves and
reflects finite returns, quantified over every typed input and complete output
tuple. The target computes primitive bindings and γ selection directly. It
specifies θ by reflexive-transitive closure of completed restarts followed by
one completed exit. The proof relates this closure to the source's inductive
`Theta.Iterate` and checks reference lookup and each nested region's scope.
`Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.observe_eq_some_iff` connects the same
relation to the [stateless institution's `Part` observation](rvsdg-nested-stateless-institution.md).

The examples check a bypass around a spinning arm, a selected θ that takes
two restarts and exits with a changed heterogeneous carry, and a selected spin
with an explicit infinite path of completed restarts. The parent swaps the
Boolean and natural-number output slots. The spin has a separate proof of no
finite return even when the arm discards all θ results. `Productive` observes
positive restarts of a particular body. Global classification of non-return,
effects, LLVM graph-region semantics and upstream SCF equivalence fall outside
this proof scope.

[Definitions](../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Defs.lean) ·
[Theorems](../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Thms.lean) ·
[Examples](../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Examples.lean) ·
[RVSDG references](rvsdg.md)

## Verify

```sh
lake build --wfail +Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Examples
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Examples
```
