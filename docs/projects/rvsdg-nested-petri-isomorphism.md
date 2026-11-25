# Renumbering live nested RVSDG firings

This development combines the [nested firing semantics](rvsdg-nested-petri.md)
and [typed graph renumbering](rvsdg-nested-isomorphism.md). The RVSDG
primitive, γ, and θ interfaces follow Reissmann, Meyer, Bahmann and
Själander, *RVSDG: An Intermediate Representation for Optimizing
Compilers*, arXiv:1912.05036v2, §§4.1–4.3. The PDF SHA-256 is
`861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

A `Renumbering` retains the chosen vertex and child maps of a typed graph
isomorphism. `Matches` compares corresponding vertex phases. Pending
places match pending places. Done places agree on their typed output
tuples. Waiting places agree on the selected child position and saved
input tuple, and their live child markings match recursively under that
child's own map. Fresh initial markings satisfy this relation. Every
typed marking has a unique counterpart in either direction.
[Definitions](../../Silmaril/SSA/RVSDG/NestedTheta/Petri/Isomorphism/Defs.lean)

The proof locates each spine firing at a numbered vertex, compares its
published input colours using the preserved wire origins, and rebuilds
the firing at the image vertex. Every sibling place remains untouched.
Entering γ creates only the paired selected arm. A θ restart uses
the matching result of the completed child, then installs fresh
markings carrying the same feedback tuple. A step inside a live child
recursively matches one step inside that child.

`step_forth` and `step_back` form a bisimulation for any pair of related
markings. They require no reachability premise. `step_iff` gives direct
preservation and reflection between corresponding source and target
markings. `trace_forth` and
`trace_back` pair finite traces one step at a time and relate every
intermediate marking. `result_eq` equates the optional full result at
any pair of related markings. These are statements about the existing
fine-grained firing relation. The previous graph evaluation invariance
theorem concerns finite returns. The trace theorem here counts actual
firings. Infinite and fair executions are outside its scope.
[Public theorems](../../Silmaril/SSA/RVSDG/NestedTheta/Petri/Isomorphism/Thms.lean)

The fixture chooses a γ arm that runs θ twice. It swaps the γ node
and its independent root sibling, and swaps two independent body
vertices inside θ. It exhibits a sibling firing while both regions
are live, checks the exact fresh restart on the renumbered graph, and
pairs all ten firings with matching full value/state observations.
[Fixture](../../tests/ssa/RVSDGNestedPetriIsomorphism.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedPetriIsomorphism.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Thms +Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms'
```
