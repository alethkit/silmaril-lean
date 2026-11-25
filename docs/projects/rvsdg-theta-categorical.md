# Categorical whole-region θ

The denotation interprets the [whole-region θ syntax](rvsdg-theta.md) with
the same typed, numbered primitive and γ body as the operational semantics.
The input and output object is the ordered Cartesian value tensor of the
carried ports. A body yields a two-way selector followed by the updated
tuple. A coproduct-preserving functor maps the value arrow into the
computation category. The routed body maps stop (tag zero) to the left
summand and continue (tag one) to the right, carrying the updated tuple
unchanged along either leg. [Definitions](../../Silmaril/SSA/RVSDG/Theta/Categorical/Defs.lean)

`Iteration.iterate` closes the right summand. `Graph.denote_unfold` gives
the Elgot fixpoint equation and accounts for the mandatory first body
execution. `Graph.denote_toTerm` uses the primitive/γ categorical agreement
to identify the graph and inductive denotations. The construction takes
place in the repository's existing Elgot categories and applies to strong
Elgot Freyd models through their coproduct-preserving value functors.
The captured loop context is the carried tuple, so this rule needs no
context external to the loop. [Theorems](../../Silmaril/SSA/RVSDG/Theta/Categorical/Thms.lean)

## Verification boundary

For every total deterministic RVSDG model, the `Part` Kleisli
specialization returns a packed tuple exactly when `Graph.Returns` holds.
It yields `Part.none` exactly when `Graph.Diverges` holds. The reverse
direction uses totality of the body evaluation to construct an infinite
sequence of continuing steps from the absence of any finite return.
These observations include returned state snapshots. Divergence observes
infinitely many completed continuing body steps. This leaves arbitrary
Petri firing schedules, θ inside arbitrary vertices, and ordered runtime
effects to separate extensions. The fixture checks a finite multi-step
return, one mandatory execution at the stopping bound, and divergence.
[Fixture](../../tests/ssa/RVSDGThetaCategorical.lean)

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Theta.Categorical.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.Theta.Categorical.Thms
lake env leanchecker Silmaril.SSA.RVSDG.Theta.Categorical.Thms
```

## Sources

The exact artifact pins are in the [categorical project sources](rvsdg-categorical.md#sources).
The operative clauses are Reissmann et al. (2020), arXiv:1912.05036v2,
§4.1.3 for tail-controlled θ, and Ghalayini and Krishnaswami (2024),
arXiv:2411.09347v1, §5.1 Definition 5.5 for the Elgot fixpoint and §5.3
for the interpretation of typed regions.
