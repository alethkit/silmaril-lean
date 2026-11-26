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
relation to the [stateless institution's `Part` observation](../semantics/rvsdg-nested-stateless-institution.md).

The examples check a bypass around a spinning arm, a selected θ that takes
two restarts and exits with a changed heterogeneous carry, and a selected spin
with an explicit infinite path of completed restarts. The parent swaps the
Boolean and natural-number output slots. The spin has a separate proof of no
finite return even when the arm discards all θ results. `Productive` observes
positive restarts of a particular body. Global classification of non-return,
effects, LLVM graph-region semantics and upstream SCF equivalence fall outside
this proof scope.

[Definitions](../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Defs.lean) ·
[Theorems](../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Thms.lean) ·
[Examples](../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Examples.lean) ·
[RVSDG references](../overview.md)

## Checked numbered PEG loops

The [whole-region θ adapter][whole-theta] takes the actual numbered body over
a stateless signature. It wraps the body's primitive labels in the empty-effect
dialect, uses the existing θ embedding, and derives `NoState` from the
data-only entry ports, primitive profiles, and typed wiring. The embedding
keeps the body's port ordering, numbered references, and isolated γ arms.

The [checked PEG adapter][peg-scoped] applies this construction to
`Bundle.compile` from the [ordered PEG θ compiler][peg-theta]. It reuses the
bundle's guard and simultaneous update schedules. Its finite-return theorem
compares the generated scoped block with the precise numbered graph in the
existing total PEG model. The SCF corollary compares it with the [native
`scf.while`][peg-scf] produced from the same bundle under the given bitvector profile.
Both observations include the complete carry tuple. The
[fixture][scoped-fixture] executes the emitted scoped block through two restarts
and a stopping activation, and checks SCF agreement for immediate exit and
16-bit overflow.

The mixed θ in [#4109][mixed-theta] has a data-only primitive row, but the
classifier consumes and returns a runtime token. In [#4277][mixed-prefix] the
θ seed and exit, the carrier conversion, and the ordered continuation all
retain that token. Those boundary profiles fail `NoState`. The classifier
also runs in `StateT σ Part` and may update the store or fail to return.
The mixed finite-return observation includes the final store and exit label.
An extension to that family needs a target with ordered effect and partial
execution semantics, with agreement on the threaded store.

[whole-theta]: ../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Theta/Thms.lean
[peg-scoped]: ../../../../Silmaril/SSA/PEG/Bridge/Theta/Region/MLIR/Scoped/Thms.lean
[peg-theta]: https://github.com/hiloopai/silmaril-lean/pull/3993
[peg-scf]: https://github.com/hiloopai/silmaril-lean/pull/4252
[scoped-fixture]: ../../../../tests/ssa/PEGStructuredTheta.lean
[mixed-theta]: https://github.com/hiloopai/silmaril-lean/pull/4109
[mixed-prefix]: https://github.com/hiloopai/silmaril-lean/pull/4277

## Verify

```sh
lake build --wfail +Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Examples PEGStructuredThetaTests
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Examples PEGStructuredThetaTests'
```
