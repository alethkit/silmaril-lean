# The ordered-state institution for nested RVSDG

A signature fixes the alphabet of value sorts and gives separate families of
pure and effectful opcodes indexed by their ordered input and output ports.
Signature morphisms map opcodes within each family at exactly those ports.
Selectors, unit state slots, and typed wiring stay fixed. An equation compares
two numbered nested RVSDG graphs at a common input and output boundary. Each
side has its own vertex signatures. [Definitions](../../Silmaril/SSA/RVSDG/NestedTheta/Institution/Defs.lean)

A model assigns value carriers, pure functions, and total `StateM σ` actions
to those families. The institution fixes the store type `σ` and uses discrete
model categories. A reduct retains the carriers and store and precomposes
the primitive interpretations with the opcode maps. Sentence translation
relabels the exact typed graph decoding recursively through all γ arms and θ
bodies, then encodes it with the same numbering. The nested open interpretation
commutes with this relabelling for a shared monad and iteration operation.
The ordered instance uses the existing lift to `StateT σ Part`. [Ordered semantics](rvsdg-nested-theta.md) · [Theorems](../../Silmaril/SSA/RVSDG/NestedTheta/Institution/Thms.lean)

Satisfaction compares the partial observations of the full returned tuple and
exact final store for every entry tuple and initial store. Identity and
composition laws for sentence translation and model reducts, together with
satisfaction in the reduct iff satisfaction of the translated equation, give
an institution in the repository's `Sign ⥤ Room` framework. By unbounded
finite adequacy, this is equivalent to agreement on each finite return of the
existing ordered relation. With total primitive actions, a missing finite
observation records only absence of a completed return. The
partial-primitive institution adds block diagnostics and productive divergence.
[Satisfaction and adequacy](../../Silmaril/SSA/RVSDG/NestedTheta/Institution/Thms.lean) · [Partial-primitive institution](rvsdg-nested-partial-institution.md)

The fixture migrates two distinct effectful opcodes to a common target opcode.
The selected γ arm contains a θ that takes one feedback step. The equation
holds in the target and its reduct. A different source model gives the same
payload on that arm but stores 2 and 20, refuting the equation. [Fixture](../../tests/ssa/RVSDGNestedThetaInstitution.lean)

## Reproduce

```sh
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.NestedTheta.Institution.Thms
lake env leanchecker Silmaril.SSA.RVSDG.NestedTheta.Institution.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.2–4.1.3, Definitions 1–3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Joseph A. Goguen and Rod M. Burstall, *Institutions: Abstract Model Theory
  for Specification and Programming* (1992), §2.1 Definition 1 and §2.5
  Definition 12. PDF SHA-256
  `f6715ca333dd03dc153a65907c1c974fa151690bb94eafffc065c363265b634d`.
  [PDF](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf) · [DOI](https://doi.org/10.1145/147508.147524)
