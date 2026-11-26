# Renumbering nested RVSDG regions

This extends the typed port-graph isomorphism from [#2228](https://github.com/hiloopai/silmaril-lean/pull/2228)
to the compositional primitive, γ and θ fragment in
[the nested θ development](rvsdg-nested-theta.md). The structural interfaces
follow Reissmann, Meyer, Bahmann and Själander, *RVSDG: An Intermediate
Representation for Optimizing Compilers*, arXiv:1912.05036v2, §§4.1–4.3.
The PDF SHA-256 is `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

Each paired region has the same ordered input and output signatures. The
local bijection preserves vertex signatures, opcodes, γ arm positions,
the θ body position, and the origin address of every operand and result.
Both vertex tables enforce topological scope through their endpoint types.
The two tables and all paired child regions may use different numberings.
[Definition](../../../../Silmaril/SSA/RVSDG/NestedTheta/Isomorphism/Defs.lean)

The proof compares type-tagged results at corresponding addresses by
induction over earlier producers. An auxiliary table records whole-vertex
success separately from port colours, including for vertices with zero
outputs. The full evaluator result requires all vertices to succeed.
Child isomorphisms give equal evaluators for each γ arm and each activation
of the θ body. `run_eq` therefore holds at every bound, and both graph
and term finite-return observations agree on the full typed tuple.
[Public theorems](../../../../Silmaril/SSA/RVSDG/NestedTheta/Isomorphism/Thms.lean)

The fixture swaps independent value and state operations at the root and
inside a θ reached through γ. It checks bound exhaustion and a successful
two-iteration return. The theorems compare finite-return observations.
The [live marking development](rvsdg-nested-petri-isomorphism.md) uses
the same vertex and child maps to transport individual Petri firings.
[Fixture](../../../../tests/ssa/RVSDGNestedThetaIsomorphism.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedThetaIsomorphism.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Isomorphism.Petri.Thms +Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms'
```
