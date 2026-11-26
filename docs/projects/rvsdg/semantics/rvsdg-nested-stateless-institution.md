# Stateless equations for nested RVSDG

A signature fixes a value alphabet and declares total operations with ordered
value and selector ports. A model supplies carriers and one total function
per declared operation. The typed numbered graph syntax admits primitives,
multiway γ and θ at any nesting depth. The admission predicate checks data
ports at every binding and region boundary, including graph entry and exit.
Equations compare the two graphs on every input, observing the entire result
in the existing nested `Part` interpretation, which agrees with the finite
structured execution relation.

Port-preserving opcode maps translate equations and induce model reducts by
precomposition. The satisfaction condition follows from reindexing the nested
interpretation. The comorphism into the
[partial ordered institution](rvsdg-nested-partial-institution.md)
uses an empty effect opcode family. The ordered port alphabet still contains
the ambient state sort. Its use is excluded by the stateless admission
predicate. The sentence translation forgets only the proof of admission.
It is injective at each signature on literal typed numbered equations,
including both graphs' numbering.

The interpretation theorem lifts a pure return into the ordered model with
the initial store unchanged. At θ, Elgot uniformity fixes the store on every
restart and naturality attaches that same store to the final result. No
primitive can report a block because a blocked attempt would require an
effect opcode. Ordered endpoint classification therefore equates absence of
a pure return with a productive-divergence witness in the ordered model.
Satisfaction reflects at any nonempty store type, including `Unit`, by
instantiating the equation at one initial store. Every stateless model
expands at the empty effect signature, so the comorphism also preserves and
reflects semantic consequence at that signature.

The fixture migrates `tick` and `spin` to `advance` and `repeat`. It
selects a γ arm containing θ, checks two feedback steps with the store
unchanged, and distinguishes termination from productive divergence. A
valid equation adds an unused γ result. A refuted equation substitutes the
spinning θ. Both equations are checked after migration and inclusion. A
separate bypass observation checks that the unselected spinning arm does
not run.

[Public API](../../../../Silmaril/SSA/RVSDG/NestedTheta/Institution/Stateless/Thms.lean) ·
[Fixture](../../../../tests/ssa/RVSDGNestedThetaStatelessInstitution.lean)

## Reproduce

```sh
make check CHECK_TARGETS="+Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Thms"
lake env leanchecker Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.2–4.1.3, Definitions 1–3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Joseph A. Goguen and Rod M. Burstall, *Institutions: Abstract Model Theory
  for Specification and Programming* (1992), §2.1 Definition 1 and
  Proposition 35. PDF SHA-256
  `f6715ca333dd03dc153a65907c1c974fa151690bb94eafffc065c363265b634d`.
  [PDF](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf) ·
  [DOI](https://doi.org/10.1145/147508.147524)
