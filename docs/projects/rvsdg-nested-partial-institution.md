# Observing partial primitives in nested RVSDG

This institution extends the [nested ordered-state equations](rvsdg-nested-ordered-institution.md)
to models with pure functions and partial `StateT σ Part` effects. Pure
functions stay total. Value sorts and the store type are fixed. Sentences are
equations between typed numbered graphs with arbitrary nesting of γ and θ.
Both sides share an ordered entry and result interface.

For each input tuple and initial store the equation compares three outcomes.

- A return observes the entire output tuple and final store in the existing
  nested Elgot denotation.
- A block records the unsuccessful primitive attempt, including its store,
  typed inputs, typed opcode and static address. The address is the path of
  enclosing (vertex, child) positions followed by the local vertex number.
  Repeated activations use the same static address.
- Productive divergence witnesses infinitely many successful, continuing
  activations of a θ, or reaches a nested child with such a witness. Each
  restart observes the whole carried tuple and store produced by the body.

Successful prefixes and θ restarts use the existing nested ordered
interpretation. A primitive action with undefined result counts as an atomic
blocked attempt. Its internal implementation is outside the model boundary.
The classification theorem gives disjoint, exhaustive endpoints. Its θ
case uses the correspondence between Elgot returns and finite body
completions, deterministic restart steps, and an infinite path of positive
restarts when a reached activation can neither stop nor report a child
endpoint. Satisfaction observes existence of productive divergence and
leaves the comparison of infinite traces outside this interface.
[Definitions](../../Silmaril/SSA/RVSDG/NestedTheta/OrderedState/Partial/Defs.lean) · [Classification](../../Silmaril/SSA/RVSDG/NestedTheta/OrderedState/Partial/Thms.lean)

Migrations preserve ordered ports, symbols' pure or effectful status, and graph
numbering. At each entry and exit signature an effect opcode map must be
injective because the failed opcode is observable. Identifying two failed
opcodes could make different source block diagnostics equal after migration.
The pure opcode maps retain the full scope of the total institution. A reduct
retains the carriers and precomposes the model's primitive interpretations.
The translated graph has exactly the relabelled abnormal observations of the
source in the reduct, including the same attempted inputs and store. This
transport and return preservation yield satisfaction iff, with the sentence
and reduct identity and composition laws in `Sign ⥤ Room`.
[Institution](../../Silmaril/SSA/RVSDG/NestedTheta/Institution/Partial/Thms.lean)

The fixture migrates two distinct effectful opcodes. Both equation sides select
a γ arm containing θ and produce no finite return. One blocks at the migrated
primitive after its first feedback, at input 1 and store 5. The other has an
explicit infinite sequence of successful restarts. The equation fails, and
the bypass arm returns its tuple with store 4 unchanged.
[Fixture](../../tests/ssa/RVSDGNestedThetaPartialInstitution.lean)

## Reproduce

```sh
make check CHECK_TARGETS="+Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Thms +Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Thms"
lake env leanchecker Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Thms
lake env leanchecker Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Thms
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
